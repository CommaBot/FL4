/-
P3 (issue #16, FL4 #71), VSpace FrameBatch (KENTRY-PLAN fb3l): **FL4's `batch_map`
refines the spec's `fbMap`** at the CSpace / VSpace relations (VsFrameMapRel's
`frame_map_rel` level).

`batch_map` is `decode_page_map` without the caller's restart and without
`check_vspace` (the batch's address space was checked by the decode; the spec's
`find_vspace_for_asid` is given, `hf`). The tails `bmap_tail`, `bmap_tail_L`,
`bmap_tail_H` are VsFrameMapRel's / VsFrameMapLRel's `map_tail*` with the
`check_vspace` step and the restart dropped (the cap write and the mapping write
from `s` and `σ` directly); `MapSpecN` is `MapSpec` without the restart.
`batch_map_{small,large,huge}_rel` walk `batch_map` for a frame cap of each size;
`batch_map_rel` dispatches on the slot's cap and states the outcome against
`fbMap` (`fbMap_frame`, `fbMap_nonPage`). `FbKeep` of the spec step: `fbk_cnode`,
`fbk_store_flush*`.
-/
import Fl4Proofs.P3.XTopJointFbDefs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

section Spec
open Fl4Spec

/-- The spec after the page-map decode, without the restart: `σ'` an outcome of the perform, which
does not fail. -/
def MapSpecN (σ : State Unit) (iv : ArchInvocation) (σ' : State Unit) : Prop :=
  match iv with
  | .invokePage pi => (([] : List Data), σ') ∈ (performPageInvocation (Z := Unit) pi σ).1 ∧
      ¬ (performPageInvocation (Z := Unit) pi σ).2
  | _ => False

theorem fb_label : invocationType fbPageMapLabel = .archInvocationLabel .x64PageMap := by
  have h : (InvocationLabel.archInvocationLabel .x64PageMap).fromEnum = dataToNat fbPageMapLabel := by decide
  unfold invocationType
  rw [if_pos ⟨_, h⟩, ← h]
  decide

theorem fbk_cnode {σ : State Unit} {p : ObjRef} {r : Nat} {cs : CnodeContents} (hk : σ.kheap p = some (.cnode r cs))
    (idx : List Bool) (a : Cap) : FbKeep σ (setCnodeSlot σ p r cs idx a) := by
  refine ⟨fun o => ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_cases e : o = p
  · subst e; exact Or.inr (Or.inr (Or.inl ⟨r, cs, Function.update cs idx (some a), hk, by simp [setCnodeSlot]⟩))
  · exact Or.inl (by simp [setCnodeSlot, e])

theorem fbk_arch {σ : State Unit} {p : ObjRef} {ao : ArchKernelObj} (hk : σ.kheap p = some (.archObj ao))
    (hn : aaType ao ≠ .aASIDPool) (ao' : ArchKernelObj) (ht : aaType ao' = aaType ao) :
    FbKeep σ (Notif.updK σ p (.archObj ao')) := by
  refine ⟨fun o => ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [Notif.updK_kheap]
  by_cases e : o = p
  · subst e; exact Or.inr (Or.inl ⟨ao, ao', hk, by rw [Function.update_self], ht, hn⟩)
  · exact Or.inl (by rw [Function.update_of_ne e])

theorem fbk_ms (σ : State Unit) (ms : MachineState) : FbKeep σ { σ with machineState := ms } :=
  ⟨fun _ => Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The spec's caps across a page map**: each one as before, or a page cap at the written slot. -/
def CapPage (σ σ' : State Unit) (sl : CslotPtr) : Prop :=
  ∀ p cref a, capOpt (σ'.kheap p) cref = some a →
    capOpt (σ.kheap p) cref = some a ∨ (p = sl.1 ∧ cref = sl.2 ∧ IsPageCap a)

theorem capPage_set {σ : State Unit} {p : ObjRef} {r : Nat} {cs : CnodeContents}
    (hk : σ.kheap p = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) {idx : List Bool} (hidx : idx.length = r)
    (a : Cap) (ha : IsPageCap a) {σ' : State Unit}
    (hσ' : ∀ q cref, capOpt (σ'.kheap q) cref = capOpt ((setCnodeSlot σ p r cs idx a).kheap q) cref) :
    CapPage σ σ' (p, idx) := by
  intro q cref b hb
  rw [hσ'] at hb
  by_cases e : q = p
  · subst e
    simp only [setCnodeSlot, Function.update_self] at hb
    have hdom : idx ∈ dom cs := by rw [hwf]; exact hidx
    rw [capOpt_cnode_set a ⟨hdom, hwf⟩ cref] at hb
    by_cases ec : cref = idx
    · subst ec
      rw [Function.update_self] at hb
      obtain rfl := Option.some.inj hb
      exact Or.inr ⟨rfl, rfl, ha⟩
    · rw [Function.update_of_ne ec, ← hk] at hb
      exact Or.inl hb
  · left
    simpa [setCnodeSlot, e] using hb

end Spec

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- `FbKeep` of a PT store and its flush (`kfoot_store_flush`). -/
theorem fbk_store_flush {L4 L3 L2 L1 : Set U64} {m : U64 → U64} {σ2 σ' : Fl4Spec.State Unit}
    (hP : PtPlaced L4 L3 L2 L1) (hR : PtRel L4 L3 L2 L1 m σ2) {q : U64} (hq : q ∈ L1) {i : U64} (hi : i.val < 512)
    (pte : Fl4Spec.PTE) (vs : Fl4Spec.ObjRef) (asid : Fl4Spec.Asid)
    (hm : ((), σ') ∈ ((Fl4Spec.storePte (Z := Unit) (peA q i).bv pte >>= fun _ =>
      Fl4Spec.invalidatePageStructureCacheAsid vs asid) σ2).1) : FbKeep σ2 σ' := by
  obtain ⟨f, hk, -⟩ := hR.l1 q hq
  have hpa := hP q (Or.inr (Or.inr (Or.inr hq)))
  have hst : Fl4Spec.storePte (Z := Unit) (peA q i).bv pte σ2 =
      ({((), updK σ2 q.bv (.archObj (.pageTable (Function.update f (Fl4Spec.ucast 9 i.bv) pte))))}, False) := by
    rw [peA_bv _ _ hi (tbl_fit hpa)]; exact storePte_at hpa hk hi pte
  rw [nd_bind_one hst] at hm
  obtain ⟨ms, rfl⟩ := doMachineOp_mem hm
  exact (fbk_arch hk (by intro h; cases h) (.pageTable (Function.update f (Fl4Spec.ucast 9 i.bv) pte)) rfl).trans
    (fbk_ms _ ms)

/-- `FbKeep` of a PD store and its flush. -/
theorem fbk_store_flush_pd {L4 L3 L2 L1 : Set U64} {m : U64 → U64} {σ2 σ' : Fl4Spec.State Unit}
    (hP : PtPlaced L4 L3 L2 L1) (hR : PtRel L4 L3 L2 L1 m σ2) {q : U64} (hq : q ∈ L2) {i : U64} (hi : i.val < 512)
    (pte : Fl4Spec.PDE) (vs : Fl4Spec.ObjRef) (asid : Fl4Spec.Asid)
    (hm : ((), σ') ∈ ((Fl4Spec.storePde (Z := Unit) (peA q i).bv pte >>= fun _ =>
      Fl4Spec.invalidatePageStructureCacheAsid vs asid) σ2).1) : FbKeep σ2 σ' := by
  obtain ⟨f, hk, -⟩ := hR.l2 q hq
  have hpa := hP q (Or.inr (Or.inr (Or.inl hq)))
  have hst : Fl4Spec.storePde (Z := Unit) (peA q i).bv pte σ2 =
      ({((), updK σ2 q.bv (.archObj (.pageDirectory (Function.update f (Fl4Spec.ucast 9 i.bv) pte))))}, False) := by
    rw [peA_bv _ _ hi (tbl_fit hpa)]; exact storePde_at hpa hk hi pte
  rw [nd_bind_one hst] at hm
  obtain ⟨ms, rfl⟩ := doMachineOp_mem hm
  exact (fbk_arch hk (by intro h; cases h) (.pageDirectory (Function.update f (Fl4Spec.ucast 9 i.bv) pte)) rfl).trans
    (fbk_ms _ ms)

/-- `FbKeep` of a PDPT store and its flush. -/
theorem fbk_store_flush_pdpt {L4 L3 L2 L1 : Set U64} {m : U64 → U64} {σ2 σ' : Fl4Spec.State Unit}
    (hP : PtPlaced L4 L3 L2 L1) (hR : PtRel L4 L3 L2 L1 m σ2) {q : U64} (hq : q ∈ L3) {i : U64} (hi : i.val < 512)
    (pte : Fl4Spec.PDPTE) (vs : Fl4Spec.ObjRef) (asid : Fl4Spec.Asid)
    (hm : ((), σ') ∈ ((Fl4Spec.storePdpte (Z := Unit) (peA q i).bv pte >>= fun _ =>
      Fl4Spec.invalidatePageStructureCacheAsid vs asid) σ2).1) : FbKeep σ2 σ' := by
  obtain ⟨f, hk, -⟩ := hR.l3 q hq
  have hpa := hP q (Or.inr (Or.inl hq))
  have hst : Fl4Spec.storePdpte (Z := Unit) (peA q i).bv pte σ2 =
      ({((), updK σ2 q.bv (.archObj (.pdPointerTable (Function.update f (Fl4Spec.ucast 9 i.bv) pte))))}, False) := by
    rw [peA_bv _ _ hi (tbl_fit hpa)]; exact storePdpte_at hpa hk hi pte
  rw [nd_bind_one hst] at hm
  obtain ⟨ms, rfl⟩ := doMachineOp_mem hm
  exact (fbk_arch hk (by intro h; cases h) (.pdPointerTable (Function.update f (Fl4Spec.ucast 9 i.bv) pte)) rfl).trans
    (fbk_ms _ ms)

/-- The caps kept by a PT store and its flush (`kfoot_store_flush`). -/
theorem capk_store_flush {L4 L3 L2 L1 : Set U64} {m : U64 → U64} {σ2 σ' : Fl4Spec.State Unit}
    (hP : PtPlaced L4 L3 L2 L1) (hR : PtRel L4 L3 L2 L1 m σ2) {q : U64} (hq : q ∈ L1) {i : U64} (hi : i.val < 512)
    (pte : Fl4Spec.PTE) (vs : Fl4Spec.ObjRef) (asid : Fl4Spec.Asid)
    (hm : ((), σ') ∈ ((Fl4Spec.storePte (Z := Unit) (peA q i).bv pte >>= fun _ =>
      Fl4Spec.invalidatePageStructureCacheAsid vs asid) σ2).1) : ∀ p cref, capOpt (σ'.kheap p) cref = capOpt (σ2.kheap p) cref := by
  obtain ⟨f, hk, -⟩ := hR.l1 q hq
  have hpa := hP q (Or.inr (Or.inr (Or.inr hq)))
  have hst : Fl4Spec.storePte (Z := Unit) (peA q i).bv pte σ2 =
      ({((), updK σ2 q.bv (.archObj (.pageTable (Function.update f (Fl4Spec.ucast 9 i.bv) pte))))}, False) := by
    rw [peA_bv _ _ hi (tbl_fit hpa)]; exact storePte_at hpa hk hi pte
  rw [nd_bind_one hst] at hm
  obtain ⟨ms, rfl⟩ := doMachineOp_mem hm
  intro p cref
  simp only [Notif.updK_kheap]
  by_cases e : p = q.bv
  · subst e; rw [Function.update_self, hk]; rfl
  · rw [Function.update_of_ne e]

/-- The caps kept by a PD store and its flush. -/
theorem capk_store_flush_pd {L4 L3 L2 L1 : Set U64} {m : U64 → U64} {σ2 σ' : Fl4Spec.State Unit}
    (hP : PtPlaced L4 L3 L2 L1) (hR : PtRel L4 L3 L2 L1 m σ2) {q : U64} (hq : q ∈ L2) {i : U64} (hi : i.val < 512)
    (pte : Fl4Spec.PDE) (vs : Fl4Spec.ObjRef) (asid : Fl4Spec.Asid)
    (hm : ((), σ') ∈ ((Fl4Spec.storePde (Z := Unit) (peA q i).bv pte >>= fun _ =>
      Fl4Spec.invalidatePageStructureCacheAsid vs asid) σ2).1) : ∀ p cref, capOpt (σ'.kheap p) cref = capOpt (σ2.kheap p) cref := by
  obtain ⟨f, hk, -⟩ := hR.l2 q hq
  have hpa := hP q (Or.inr (Or.inr (Or.inl hq)))
  have hst : Fl4Spec.storePde (Z := Unit) (peA q i).bv pte σ2 =
      ({((), updK σ2 q.bv (.archObj (.pageDirectory (Function.update f (Fl4Spec.ucast 9 i.bv) pte))))}, False) := by
    rw [peA_bv _ _ hi (tbl_fit hpa)]; exact storePde_at hpa hk hi pte
  rw [nd_bind_one hst] at hm
  obtain ⟨ms, rfl⟩ := doMachineOp_mem hm
  intro p cref
  simp only [Notif.updK_kheap]
  by_cases e : p = q.bv
  · subst e; rw [Function.update_self, hk]; rfl
  · rw [Function.update_of_ne e]

/-- The caps kept by a PDPT store and its flush. -/
theorem capk_store_flush_pdpt {L4 L3 L2 L1 : Set U64} {m : U64 → U64} {σ2 σ' : Fl4Spec.State Unit}
    (hP : PtPlaced L4 L3 L2 L1) (hR : PtRel L4 L3 L2 L1 m σ2) {q : U64} (hq : q ∈ L3) {i : U64} (hi : i.val < 512)
    (pte : Fl4Spec.PDPTE) (vs : Fl4Spec.ObjRef) (asid : Fl4Spec.Asid)
    (hm : ((), σ') ∈ ((Fl4Spec.storePdpte (Z := Unit) (peA q i).bv pte >>= fun _ =>
      Fl4Spec.invalidatePageStructureCacheAsid vs asid) σ2).1) : ∀ p cref, capOpt (σ'.kheap p) cref = capOpt (σ2.kheap p) cref := by
  obtain ⟨f, hk, -⟩ := hR.l3 q hq
  have hpa := hP q (Or.inr (Or.inl hq))
  have hst : Fl4Spec.storePdpte (Z := Unit) (peA q i).bv pte σ2 =
      ({((), updK σ2 q.bv (.archObj (.pdPointerTable (Function.update f (Fl4Spec.ucast 9 i.bv) pte))))}, False) := by
    rw [peA_bv _ _ hi (tbl_fit hpa)]; exact storePdpte_at hpa hk hi pte
  rw [nd_bind_one hst] at hm
  obtain ⟨ms, rfl⟩ := doMachineOp_mem hm
  intro p cref
  simp only [Notif.updK_kheap]
  by_cases e : p = q.bv
  · subst e; rw [Function.update_self, hk]; rfl
  · rw [Function.update_of_ne e]

set_option hygiene false in
/-- The batch map from the rights on (`map_tail` without `check_vspace` and the restart). -/
macro "bmap_tail" : tactic => `(tactic| (
  simp only [bind_ok, from_word_eq]
  obtain ⟨m, hm, hm1, hm3, hmv⟩ := vm_mask rt hfw (rightsW a1)
  rw [hm]
  apply ok_bind_spec
  rw [show core.num.U64.wrapping_sub 4096#u64 1#u64 = 4095#u64 from eq_of_bv (by rw [core.num.U64.wrapping_sub_bv_eq]; decide)]
  by_cases hal : (a0 &&& 4095#u64) = 0#u64
  · have : ((a0 &&& 4095#u64) != 0#u64) = false := by simp [hal]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    -- #65: `large` is rebound by a match on the size.
    apply ok_bind_spec
    refine WP.spec_bind (WP.spec_and (page_entry_slot_small s σ hPt hPP hp1 a0 hvU)
      (page_entry_slot_small_walk s p1 a0 hvU)) ?_
    rintro r3 ⟨⟨hsl, hse⟩, hwk⟩
    cases r3 with
    | Err lf =>
      obtain ⟨n, rfl, hsp⟩ := hse _ rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from]
      simp only [Bind.bind, bind_ok]
      exact (WP.spec_ok _).2 (Or.inl ⟨_, .failedLookup false (.missingCapability n.val), rfl,
        Or.inl (Or.inl (by simp [SysErrRel, LookupFaultRel])),
        hdec.trans (mapTail_noSlot hf ((al12 a0).1 hal) hsp), rfl, rfl⟩)
    | Ok sl =>
      obtain ⟨hsp, q, hq, rfl⟩ := hsl _ rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, layout.paddr]
      simp only [frame_address_plain, layout.paddr, bind_ok]
      refine WP.spec_bind (make_user_page_4k s _ _ m) ?_
      rintro e ⟨xd, he⟩
      have hpte := pte_of_make (vmOk_of hm1 hm3) he
      rw [hpa] at hpte
      simp only [paddr_bv, attr_defer, vm_eq (rightsW a1) a1 rfl hmv] at hpte
      obtain ⟨cs, hkc, hwf, -⟩ := hSt.cnode pc r hpc
      have hkc1 : σ.kheap pc.bv = some (.cnode r cs) := hkc
      have hSt1 := hSt
      have hSV1 := hSV
      have hR1 := hR
      have hPt1 := hPt
      have hS1 := hS
      have hk1 : L.ksb s = L.ksb s := rfl
      set nc : Fl4Spec.Cap := .archObjectCap (.pageCap dev ptr.bv (vmRightsOf rt) .vmVSpaceMap .x64SmallPage
        (some (as1.bv, a0.bv))) with hnc
      have hca : CapRel (.Frame ptr .Small rt dev true false as1 a0) nc := ⟨hfw, rfl⟩
      have hew : EncWf (.Frame ptr .Small rt dev true false as1 a0) := ⟨hfe.1, hfe.2.1, has2, hva⟩
      have hxsl : IsSlot th (cslotAddr (pc.bv, idx)) :=
        (show AbsSlot th (pc.bv, idx) from ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩).isSlot
      refine WP.spec_bind (WP.spec_and (set_cap_refines th s σ hSt1 hSV1 hPl hpc hidx _ _ hca (by exact hfcv) hew)
        (WP.spec_and (set_cap_spec (L := L) _ s _) (set_cap_foot hPl hxsl s _ hew))) ?_
      rintro s2 ⟨⟨σ2, hsc, hSt2, hSV2, -, -, -, hfr2⟩, hs2, hF2, hcv2⟩
      have hσ2 : σ2 = setCnodeSlot σ pc.bv r cs idx nc := by
        rw [setCap_cnode nc hkc1 hwf hidx] at hsc
        have := congrArg Prod.fst hsc
        simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
        exact this.symm
      subst hσ2
      have hks2 : L.ksb s2 = L.ksb s := by rw [hs2]; simp [hk1]
      have hxs : IsSlotAt th pc (blVal 0 idx) := Or.inl ⟨r, hpc, hidx ▸ blVal_lt idx⟩
      have hx0 : cslotAddr (pc.bv, idx) = slotOf pc (blVal 0 idx) := slotAddr_ofBl pc idx
      have hfrV : ∀ b, VsWrite P (L.ksb s) b → L.mem s2 b = L.mem s b := by
        intro b hb
        obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs (hD b hb)
        exact hfr2 b (hb.aligned hVP) (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
      have hpools : ∀ q ∈ P, (setCnodeSlot σ pc.bv r cs idx nc).kheap q.bv = σ.kheap q.bv := by
        intro q hq
        obtain ⟨g, hg, -⟩ := hR1.pool q hq
        have : q.bv ≠ pc.bv := kheap_ne hg hkc1 (fun _ h1 h2 => by subst h1; cases h2)
        simp [setCnodeSlot, this]
      have hR2 : VsRel P (L.mem s2) (L.ksb s2) (setCnodeSlot σ pc.bv r cs idx nc) := by
        rw [hks2]; rw [hk1] at hR1
        exact hR1.frame hfrV rfl hpools
      have hWs : WritesIn st s s2 (SlotW th) := by
        refine ⟨by rw [hs2]; simp, by rw [hs2]; simp, fun b hb hn => ?_⟩
        obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs hn
        exact hfr2 b hb (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
      have hS2 := hH.capStable _ _ a _ _ hS1 hWs ⟨pc.bv, r, cs, idx, nc, hkc1, rfl⟩
      have hPt2 : PtRel L4 L3 L2 L1 (L.mem s2) (setCnodeSlot σ pc.bv r cs idx nc) := by
        refine hPt1.frame (fun b hb => ?_) (fun q hq => ?_)
        · obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs (hPS b hb)
          exact hfr2 b (hb.aligned hPP) (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
        · obtain ⟨ao, hao⟩ := hPt1.arch hq
          have : q.bv ≠ pc.bv := kheap_ne hao hkc1 (fun _ h1 h2 => by subst h1; cases h2)
          simp [setCnodeSlot, this]
      have hPS1 : ∀ b, PtW L1 b → ¬ SlotW th b := by
        rintro b ⟨p, hp, i, hi, hb⟩
        exact hPS b ⟨p, Or.inr (Or.inr (Or.inr hp)), i, hi, hb⟩
      have hMR : MapRel st th P L1 SR s2 a (setCnodeSlot σ pc.bv r cs idx nc) :=
        ⟨hS2, hSt2, hSV2, hR2, by rw [hks2]; exact hVP, by rw [hks2]; exact hPV⟩
      refine WP.spec_bind (write_mapping_rel (hH.map.ext hPl hPS1) s2 a _ hPt2 hPP hMR hq (vIdx_lt a0 12) e _ hpte
        as1 a0 _ (Fl4Spec.addrFromPPtr p1.bv)) ?_
      rintro ⟨s3, a3⟩ ⟨hr3, hnf, σ', hm', hPt3, hS3, hSt3, hSV3, hR3, -, -⟩
      have hbo : OutsideObjects th (peA q (vIdx a0 12)) := hPO _ ⟨q, Or.inr (Or.inr (Or.inr hq)), _, vIdx_lt a0 12, rfl⟩
      simp only at hr3
      refine (WP.spec_ok _).2 (Or.inr ⟨rfl, _, σ', hdec.trans (mapTail_ok hf ((al12 a0).1 hal) hsp), ?_,
        hSt3, hSV3, hR3, hPt3, hS3, ?_, ?_, ?_, ?_, ?_, ?_⟩)
      · unfold MapSpecN mapInv
        dsimp only
        exact performMap_mem (setCap_cnode nc hkc1 hwf hidx) hm' hnf
      · rw [hr3]
        exact hF2.trans (SlotFoot.wr_out hPl s2 hbo _)
      · rw [hr3, capV_wr_out hPl hxsl s2 hbo, hcv2]; exact ⟨⟨rfl, rfl, rfl, rfl⟩, fun _ _ _ _ _ h => by simp only [VCapOK, frameCapOf] at h ⊢; exact ⟨fun _ => has1, h.2.1, fun _ => hvU⟩⟩
      · exact (KFoot.cnode hkc1 hwf idx nc).trans
          (kfoot_store_flush hPP hPt2 hq (vIdx_lt a0 12) _ _ _ hm')
      · exact (fbk_cnode hkc1 idx nc).trans
          (fbk_store_flush hPP hPt2 hq (vIdx_lt a0 12) _ _ _ hm')
      · exact capPage_set hkc1 hwf hidx nc trivial
          (capk_store_flush hPP hPt2 hq (vIdx_lt a0 12) _ _ _ hm')
      · -- (int5, F1 stage 5) `MapLeafF`
        obtain ⟨f2, -, hko2, -, hAs2⟩ := store_flush_shape hPP hPt2 hq (vIdx_lt a0 12) _ _ _ hm'
        have hc1k := cnode_keep hkc1 idx nc
        obtain ⟨q', hW1, hq'⟩ := hwk _ rfl
        refine ⟨True.intro, by rw [hr3, capV_wr_out hPl hxsl s2 hbo, hcv2]; exact True.intro,
          by rw [hAs2]; exact hc1k.1, as1, p1, q, has1, has2, hf, ?_,
          Or.inl (by rw [peA_base_inj hq']; exact hW1)⟩
        rintro q2 ⟨ao, hao⟩ hne
        have h1 : q2.bv ≠ q.bv := fun h => hne (eq_of_bv h)
        exact (hko2 _ h1).trans (hc1k.2 _ _ hao)
  · have : ((a0 &&& 4095#u64) != 0#u64) = true := by simp [hal]
    simp only [this, ↓reduceIte]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, _, rfl, Or.inr ⟨rfl, rfl⟩,
      hdec.trans (mapTail_unaligned hf (fun h => hal ((al12 a0).2 h))), rfl, rfl⟩)))


set_option hygiene false in
/-- The batch map from the rights on (`map_tail` without `check_vspace` and the restart). -/
macro "bmap_tail_L" : tactic => `(tactic| (
  simp only [bind_ok, from_word_eq]
  obtain ⟨m, hm, hm1, hm3, hmv⟩ := vm_mask rt hfw (rightsW a1)
  rw [hm]
  apply ok_bind_spec
  rw [show core.num.U64.wrapping_sub 2097152#u64 1#u64 = 2097151#u64 from eq_of_bv (by rw [core.num.U64.wrapping_sub_bv_eq]; decide)]
  by_cases hal : (a0 &&& 2097151#u64) = 0#u64
  · have : ((a0 &&& 2097151#u64) != 0#u64) = false := by simp [hal]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    -- #65: `large` is rebound by a match on the size.
    apply ok_bind_spec
    refine WP.spec_bind (WP.spec_and (page_entry_slot_large s σ hPt hPP hp1 a0 hvU)
      (page_entry_slot_large_walk s p1 a0 hvU)) ?_
    rintro r3 ⟨⟨hsl, hse⟩, hwk⟩
    cases r3 with
    | Err lf =>
      rcases hse _ rfl with ⟨n, rfl, hsp⟩ | ⟨rfl, y, hsp, a', b', c', hg⟩
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        simp only [Bind.bind, bind_ok]
        exact (WP.spec_ok _).2 (Or.inl ⟨_, .failedLookup false (.missingCapability n.val), rfl,
          Or.inl (Or.inl (by simp [SysErrRel, LookupFaultRel])),
          hdec.trans (mapTailL_noSlot hf ((al21 a0).1 hal) hsp), rfl, rfl⟩)
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        simp only [Bind.bind, bind_ok]
        exact (WP.spec_ok _).2 (Or.inl ⟨_, .deleteFirst, rfl,
          Or.inl (Or.inl (show SysErrRel (.Sys .DeleteFirst) .deleteFirst from trivial)),
          hdec.trans (mapTailL_used hf ((al21 a0).1 hal) hsp hg), rfl, rfl⟩)
    | Ok sl =>
      obtain ⟨hsp, q, hq, rfl, d, hgd, hd⟩ := hsl _ rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, layout.paddr]
      simp only [frame_address_plain, layout.paddr, bind_ok]
      refine WP.spec_bind (make_user_page_large s _ _ m) ?_
      rintro e ⟨xd, he⟩
      have hpte := pde_of_make_large (L1 := L1) (vmOk_of hm1 hm3) hpa he
      simp only [paddr_bv, attr_defer, vm_eq (rightsW a1) a1 rfl hmv] at hpte
      obtain ⟨cs, hkc, hwf, -⟩ := hSt.cnode pc r hpc
      have hkc1 : σ.kheap pc.bv = some (.cnode r cs) := hkc
      have hSt1 := hSt
      have hSV1 := hSV
      have hR1 := hR
      have hPt1 := hPt
      have hS1 := hS
      have hk1 : L.ksb s = L.ksb s := rfl
      set nc : Fl4Spec.Cap := .archObjectCap (.pageCap dev ptr.bv (vmRightsOf rt) .vmVSpaceMap .x64LargePage
        (some (as1.bv, a0.bv))) with hnc
      have hca : CapRel (.Frame ptr .Large rt dev true false as1 a0) nc := ⟨hfw, rfl⟩
      have hew : EncWf (.Frame ptr .Large rt dev true false as1 a0) := ⟨hfe.1, hfe.2.1, has2, hva⟩
      have hxsl : IsSlot th (cslotAddr (pc.bv, idx)) :=
        (show AbsSlot th (pc.bv, idx) from ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩).isSlot
      refine WP.spec_bind (WP.spec_and (set_cap_refines th s σ hSt1 hSV1 hPl hpc hidx _ _ hca (by exact hfcv) hew)
        (WP.spec_and (set_cap_spec (L := L) _ s _) (set_cap_foot hPl hxsl s _ hew))) ?_
      rintro s2 ⟨⟨σ2, hsc, hSt2, hSV2, -, -, -, hfr2⟩, hs2, hF2, hcv2⟩
      have hσ2 : σ2 = setCnodeSlot σ pc.bv r cs idx nc := by
        rw [setCap_cnode nc hkc1 hwf hidx] at hsc
        have := congrArg Prod.fst hsc
        simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
        exact this.symm
      subst hσ2
      have hks2 : L.ksb s2 = L.ksb s := by rw [hs2]; simp [hk1]
      have hxs : IsSlotAt th pc (blVal 0 idx) := Or.inl ⟨r, hpc, hidx ▸ blVal_lt idx⟩
      have hx0 : cslotAddr (pc.bv, idx) = slotOf pc (blVal 0 idx) := slotAddr_ofBl pc idx
      have hfrV : ∀ b, VsWrite P (L.ksb s) b → L.mem s2 b = L.mem s b := by
        intro b hb
        obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs (hD b hb)
        exact hfr2 b (hb.aligned hVP) (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
      have hpools : ∀ q ∈ P, (setCnodeSlot σ pc.bv r cs idx nc).kheap q.bv = σ.kheap q.bv := by
        intro q hq
        obtain ⟨g, hg, -⟩ := hR1.pool q hq
        have : q.bv ≠ pc.bv := kheap_ne hg hkc1 (fun _ h1 h2 => by subst h1; cases h2)
        simp [setCnodeSlot, this]
      have hR2 : VsRel P (L.mem s2) (L.ksb s2) (setCnodeSlot σ pc.bv r cs idx nc) := by
        rw [hks2]; rw [hk1] at hR1
        exact hR1.frame hfrV rfl hpools
      have hWs : WritesIn st s s2 (SlotW th) := by
        refine ⟨by rw [hs2]; simp, by rw [hs2]; simp, fun b hb hn => ?_⟩
        obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs hn
        exact hfr2 b hb (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
      have hS2 := hH.capStable _ _ a _ _ hS1 hWs ⟨pc.bv, r, cs, idx, nc, hkc1, rfl⟩
      have hPt2 : PtRel L4 L3 L2 L1 (L.mem s2) (setCnodeSlot σ pc.bv r cs idx nc) := by
        refine hPt1.frame (fun b hb => ?_) (fun q hq => ?_)
        · obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs (hPS b hb)
          exact hfr2 b (hb.aligned hPP) (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
        · obtain ⟨ao, hao⟩ := hPt1.arch hq
          have : q.bv ≠ pc.bv := kheap_ne hao hkc1 (fun _ h1 h2 => by subst h1; cases h2)
          simp [setCnodeSlot, this]
      have hMR : MapRelA st th P L4 L3 L2 L1 SR s2 a (setCnodeSlot σ pc.bv r cs idx nc) :=
        ⟨hS2, hSt2, hSV2, hR2, by rw [hks2]; exact hVP, by rw [hks2]; exact hPV⟩
      refine WP.spec_bind (write_mapping_rel_pd (hH.map.ext hPl hPS) s2 a _ hPt2 hPP hMR hq (vIdx_lt a0 21) e _ hpte
        as1 a0 _ (Fl4Spec.addrFromPPtr p1.bv)) ?_
      rintro ⟨s3, a3⟩ ⟨hr3, hnf, σ', hm', hPt3, hS3, hSt3, hSV3, hR3, -, -⟩
      have hbo : OutsideObjects th (peA q (vIdx a0 21)) := hPO _ ⟨q, Or.inr (Or.inr (Or.inl hq)), _, vIdx_lt a0 21, rfl⟩
      simp only at hr3
      refine (WP.spec_ok _).2 (Or.inr ⟨rfl, _, σ', hdec.trans (mapTailL_ok hf ((al21 a0).1 hal) hsp hgd hd), ?_,
        hSt3, hSV3, hR3, hPt3, hS3, ?_, ?_, ?_, ?_, ?_, ?_⟩)
      · unfold MapSpecN mapInvL
        dsimp only
        exact performLMap_mem (setCap_cnode nc hkc1 hwf hidx) hm' hnf
      · rw [hr3]
        exact hF2.trans (SlotFoot.wr_out hPl s2 hbo _)
      · rw [hr3, capV_wr_out hPl hxsl s2 hbo, hcv2]; exact ⟨⟨rfl, rfl, rfl, rfl⟩, fun _ _ _ _ _ h => by simp only [VCapOK, frameCapOf] at h ⊢; exact ⟨fun _ => has1, h.2.1, fun _ => hvU⟩⟩
      · exact (KFoot.cnode hkc1 hwf idx nc).trans
          (kfoot_store_flush_pd hPP hPt2 hq (vIdx_lt a0 21) _ _ _ hm')
      · exact (fbk_cnode hkc1 idx nc).trans
          (fbk_store_flush_pd hPP hPt2 hq (vIdx_lt a0 21) _ _ _ hm')
      · exact capPage_set hkc1 hwf hidx nc trivial
          (capk_store_flush_pd hPP hPt2 hq (vIdx_lt a0 21) _ _ _ hm')
      · -- (int5, F1 stage 5) `MapLeafF`
        obtain ⟨fq, hkq, -⟩ := hPt.l2 q hq
        have hqa := hPP q (Or.inr (Or.inr (Or.inl hq)))
        have hg : Fl4Spec.getPde (Z := Unit) (peA q (vIdx a0 21)).bv σ =
            ({(fq (Fl4Spec.ucast 9 (vIdx a0 21).bv), σ)}, False) := by
          rw [peA_bv _ _ (vIdx_lt a0 21) (tbl_fit hqa)]; exact getPde_at hqa hkq (vIdx_lt a0 21)
        have hdf : d = fq (Fl4Spec.ucast 9 (vIdx a0 21).bv) := by
          have h := congrArg Prod.fst (hgd.symm.trans hg)
          simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq] at h
          exact h.1
        obtain ⟨f2, hk2, hko2, hk2', hAs2⟩ := store_flush_shape_pd hPP hPt2 hq (vIdx_lt a0 21) _ _ _ hm'
        have hc1k := cnode_keep hkc1 idx nc
        have h2q := (hc1k.2 _ _ hkq).trans hkq
        rw [h2q] at hk2
        cases hk2
        obtain ⟨q', hW2, hq'⟩ := hwk _ rfl
        refine ⟨True.intro, by rw [hr3, capV_wr_out hPl hxsl s2 hbo, hcv2]; exact True.intro,
          by rw [hAs2]; exact hc1k.1, as1, p1, q, has1, has2, hf, ?_,
          Or.inr (Or.inl ⟨by rw [peA_base_inj hq']; exact hW2, _, vIdx a0 21, _, vIdx_lt a0 21, hkq,
            by rw [← hdf]; exact hd, Or.inr ⟨_, _, _, rfl⟩, hk2'⟩)⟩
        rintro q2 ⟨ao, hao⟩ hne
        have h1 : q2.bv ≠ q.bv := fun h => hne (eq_of_bv h)
        exact (hko2 _ h1).trans (hc1k.2 _ _ hao)
  · have : ((a0 &&& 2097151#u64) != 0#u64) = true := by simp [hal]
    simp only [this, ↓reduceIte]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, _, rfl, Or.inr ⟨rfl, rfl⟩,
      hdec.trans (mapTailL_unaligned hf (fun h => hal ((al21 a0).2 h))), rfl, rfl⟩)))


set_option hygiene false in
/-- The batch map from the rights on (`map_tail` without `check_vspace` and the restart). -/
macro "bmap_tail_H" : tactic => `(tactic| (
  simp only [bind_ok, from_word_eq]
  obtain ⟨m, hm, hm1, hm3, hmv⟩ := vm_mask rt hfw (rightsW a1)
  rw [hm]
  apply ok_bind_spec
  rw [show core.num.U64.wrapping_sub 1073741824#u64 1#u64 = 1073741823#u64 from eq_of_bv (by rw [core.num.U64.wrapping_sub_bv_eq]; decide)]
  by_cases hal : (a0 &&& 1073741823#u64) = 0#u64
  · have : ((a0 &&& 1073741823#u64) != 0#u64) = false := by simp [hal]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    -- #65: the size match binds `(fs, huge)`; a 1 GiB map needs the feature bit.
    first
      | rw [huge_pages_eq]
      | (apply ok_bind_spec; try dsimp only; try simp only [↓reduceIte]; rw [huge_pages_eq])
    apply ok_bind_spec
    have hHg : HugeRel (L.mem s) (L.ksb s) σ := hH.huge s a σ hS
    unfold HugeRel at hHg
    by_cases hhb : ((L.mem s (core.num.U64.wrapping_add (L.ksb s) layout.ks.FEATURES) &&&
        layout.ks.FEATURE_HUGE_PAGES) != 0#u64) = true
    rotate_left
    · have hσh : σ.archState.x64Plat.hugePages = false := by rw [← hHg]; exact Bool.eq_false_iff.mpr hhb
      simp only [hhb, Bool.false_eq_true, ↓reduceIte, error.illegal, bind_ok]
      exact (WP.spec_ok _).2 (Or.inl ⟨_, .illegalOperation, rfl,
        Or.inl (Or.inl (show SysErrRel (.Sys .IllegalOperation) .illegalOperation from trivial)),
        hdec.trans (mapTailH_noHuge hf ((al30 a0).1 hal) hσh), rfl, rfl⟩)
    have hσh : σ.archState.x64Plat.hugePages = true := by rw [← hHg]; exact hhb
    simp only [hhb, ↓reduceIte]
    apply ok_bind_spec
    refine WP.spec_bind (WP.spec_and (page_entry_slot_huge s σ hPt hPP hp1 a0 hvU)
      (page_entry_slot_huge_walk s p1 a0 hvU)) ?_
    rintro r3 ⟨⟨hsl, hse⟩, hwk⟩
    cases r3 with
    | Err lf =>
      rcases hse _ rfl with ⟨n, rfl, hsp⟩ | ⟨rfl, y, hsp, a', b', c', hg⟩
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        simp only [Bind.bind, bind_ok]
        exact (WP.spec_ok _).2 (Or.inl ⟨_, .failedLookup false (.missingCapability n.val), rfl,
          Or.inl (Or.inl (by simp [SysErrRel, LookupFaultRel])),
          hdec.trans (mapTailH_noSlot hf ((al30 a0).1 hal) hσh hsp), rfl, rfl⟩)
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        simp only [Bind.bind, bind_ok]
        exact (WP.spec_ok _).2 (Or.inl ⟨_, .deleteFirst, rfl,
          Or.inl (Or.inl (show SysErrRel (.Sys .DeleteFirst) .deleteFirst from trivial)),
          hdec.trans (mapTailH_used hf ((al30 a0).1 hal) hσh hsp hg), rfl, rfl⟩)
    | Ok sl =>
      obtain ⟨hsp, q, hq, rfl, d, hgd, hd⟩ := hsl _ rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, layout.paddr]
      simp only [frame_address_plain, layout.paddr, bind_ok]
      refine WP.spec_bind (make_user_page_large s _ _ m) ?_
      rintro e ⟨xd, he⟩
      have hpte := pdpte_of_make_huge (L2 := L2) (vmOk_of hm1 hm3) hpa he
      simp only [paddr_bv, attr_defer, vm_eq (rightsW a1) a1 rfl hmv] at hpte
      obtain ⟨cs, hkc, hwf, -⟩ := hSt.cnode pc r hpc
      have hkc1 : σ.kheap pc.bv = some (.cnode r cs) := hkc
      have hSt1 := hSt
      have hSV1 := hSV
      have hR1 := hR
      have hPt1 := hPt
      have hS1 := hS
      have hk1 : L.ksb s = L.ksb s := rfl
      set nc : Fl4Spec.Cap := .archObjectCap (.pageCap dev ptr.bv (vmRightsOf rt) .vmVSpaceMap .x64HugePage
        (some (as1.bv, a0.bv))) with hnc
      have hca : CapRel (.Frame ptr .Huge rt dev true false as1 a0) nc := ⟨hfw, rfl⟩
      have hew : EncWf (.Frame ptr .Huge rt dev true false as1 a0) := ⟨hfe.1, hfe.2.1, has2, hva⟩
      have hxsl : IsSlot th (cslotAddr (pc.bv, idx)) :=
        (show AbsSlot th (pc.bv, idx) from ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩).isSlot
      refine WP.spec_bind (WP.spec_and (set_cap_refines th s σ hSt1 hSV1 hPl hpc hidx _ _ hca (by exact hfcv) hew)
        (WP.spec_and (set_cap_spec (L := L) _ s _) (set_cap_foot hPl hxsl s _ hew))) ?_
      rintro s2 ⟨⟨σ2, hsc, hSt2, hSV2, -, -, -, hfr2⟩, hs2, hF2, hcv2⟩
      have hσ2 : σ2 = setCnodeSlot σ pc.bv r cs idx nc := by
        rw [setCap_cnode nc hkc1 hwf hidx] at hsc
        have := congrArg Prod.fst hsc
        simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
        exact this.symm
      subst hσ2
      have hks2 : L.ksb s2 = L.ksb s := by rw [hs2]; simp [hk1]
      have hxs : IsSlotAt th pc (blVal 0 idx) := Or.inl ⟨r, hpc, hidx ▸ blVal_lt idx⟩
      have hx0 : cslotAddr (pc.bv, idx) = slotOf pc (blVal 0 idx) := slotAddr_ofBl pc idx
      have hfrV : ∀ b, VsWrite P (L.ksb s) b → L.mem s2 b = L.mem s b := by
        intro b hb
        obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs (hD b hb)
        exact hfr2 b (hb.aligned hVP) (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
      have hpools : ∀ q ∈ P, (setCnodeSlot σ pc.bv r cs idx nc).kheap q.bv = σ.kheap q.bv := by
        intro q hq
        obtain ⟨g, hg, -⟩ := hR1.pool q hq
        have : q.bv ≠ pc.bv := kheap_ne hg hkc1 (fun _ h1 h2 => by subst h1; cases h2)
        simp [setCnodeSlot, this]
      have hR2 : VsRel P (L.mem s2) (L.ksb s2) (setCnodeSlot σ pc.bv r cs idx nc) := by
        rw [hks2]; rw [hk1] at hR1
        exact hR1.frame hfrV rfl hpools
      have hWs : WritesIn st s s2 (SlotW th) := by
        refine ⟨by rw [hs2]; simp, by rw [hs2]; simp, fun b hb hn => ?_⟩
        obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs hn
        exact hfr2 b hb (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
      have hS2 := hH.capStable _ _ a _ _ hS1 hWs ⟨pc.bv, r, cs, idx, nc, hkc1, rfl⟩
      have hPt2 : PtRel L4 L3 L2 L1 (L.mem s2) (setCnodeSlot σ pc.bv r cs idx nc) := by
        refine hPt1.frame (fun b hb => ?_) (fun q hq => ?_)
        · obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs (hPS b hb)
          exact hfr2 b (hb.aligned hPP) (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
        · obtain ⟨ao, hao⟩ := hPt1.arch hq
          have : q.bv ≠ pc.bv := kheap_ne hao hkc1 (fun _ h1 h2 => by subst h1; cases h2)
          simp [setCnodeSlot, this]
      have hMR : MapRelA st th P L4 L3 L2 L1 SR s2 a (setCnodeSlot σ pc.bv r cs idx nc) :=
        ⟨hS2, hSt2, hSV2, hR2, by rw [hks2]; exact hVP, by rw [hks2]; exact hPV⟩
      refine WP.spec_bind (write_mapping_rel_pdpt (hH.map.ext hPl hPS) s2 a _ hPt2 hPP hMR hq (vIdx_lt a0 30) e _ hpte
        as1 a0 _ (Fl4Spec.addrFromPPtr p1.bv)) ?_
      rintro ⟨s3, a3⟩ ⟨hr3, hnf, σ', hm', hPt3, hS3, hSt3, hSV3, hR3, -, -⟩
      have hbo : OutsideObjects th (peA q (vIdx a0 30)) := hPO _ ⟨q, Or.inr (Or.inl hq), _, vIdx_lt a0 30, rfl⟩
      simp only at hr3
      refine (WP.spec_ok _).2 (Or.inr ⟨rfl, _, σ', hdec.trans (mapTailH_ok hf ((al30 a0).1 hal) hσh hsp hgd hd), ?_,
        hSt3, hSV3, hR3, hPt3, hS3, ?_, ?_, ?_, ?_, ?_, ?_⟩)
      · unfold MapSpecN mapInvH
        dsimp only
        exact performHMap_mem (setCap_cnode nc hkc1 hwf hidx) hm' hnf
      · rw [hr3]
        exact hF2.trans (SlotFoot.wr_out hPl s2 hbo _)
      · rw [hr3, capV_wr_out hPl hxsl s2 hbo, hcv2]; exact ⟨⟨rfl, rfl, rfl, rfl⟩, fun _ _ _ _ _ h => by simp only [VCapOK, frameCapOf] at h ⊢; exact ⟨fun _ => has1, h.2.1, fun _ => hvU⟩⟩
      · exact (KFoot.cnode hkc1 hwf idx nc).trans
          (kfoot_store_flush_pdpt hPP hPt2 hq (vIdx_lt a0 30) _ _ _ hm')
      · exact (fbk_cnode hkc1 idx nc).trans
          (fbk_store_flush_pdpt hPP hPt2 hq (vIdx_lt a0 30) _ _ _ hm')
      · exact capPage_set hkc1 hwf hidx nc trivial
          (capk_store_flush_pdpt hPP hPt2 hq (vIdx_lt a0 30) _ _ _ hm')
      · -- (int5, F1 stage 5) `MapLeafF`
        obtain ⟨fq, hkq, -⟩ := hPt.l3 q hq
        have hqa := hPP q (Or.inr (Or.inl hq))
        have hg : Fl4Spec.getPdpte (Z := Unit) (peA q (vIdx a0 30)).bv σ =
            ({(fq (Fl4Spec.ucast 9 (vIdx a0 30).bv), σ)}, False) := by
          rw [peA_bv _ _ (vIdx_lt a0 30) (tbl_fit hqa)]; exact getPdpte_at hqa hkq (vIdx_lt a0 30)
        have hdf : d = fq (Fl4Spec.ucast 9 (vIdx a0 30).bv) := by
          have h := congrArg Prod.fst (hgd.symm.trans hg)
          simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq] at h
          exact h.1
        obtain ⟨f2, hk2, hko2, hk2', hAs2⟩ := store_flush_shape_pdpt hPP hPt2 hq (vIdx_lt a0 30) _ _ _ hm'
        have hc1k := cnode_keep hkc1 idx nc
        have h2q := (hc1k.2 _ _ hkq).trans hkq
        rw [h2q] at hk2
        cases hk2
        obtain ⟨q', hW2, hq'⟩ := hwk _ rfl
        refine ⟨True.intro, by rw [hr3, capV_wr_out hPl hxsl s2 hbo, hcv2]; exact True.intro,
          by rw [hAs2]; exact hc1k.1, as1, p1, q, has1, has2, hf, ?_,
          Or.inr (Or.inr ⟨by rw [peA_base_inj hq']; exact hW2, _, vIdx a0 30, _, vIdx_lt a0 30, hkq,
            by rw [← hdf]; exact hd, Or.inr ⟨_, _, _, rfl⟩, hk2'⟩)⟩
        rintro q2 ⟨ao, hao⟩ hne
        have h1 : q2.bv ≠ q.bv := fun h => hne (eq_of_bv h)
        exact (hko2 _ h1).trans (hc1k.2 _ _ hao)
  · have : ((a0 &&& 1073741823#u64) != 0#u64) = true := by simp [hal]
    simp only [this, ↓reduceIte]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, _, rfl, Or.inr ⟨rfl, rfl⟩,
      hdec.trans (mapTailH_unaligned hf (fun h => hal ((al30 a0).2 h))), rfl, rfl⟩)))



set_option maxHeartbeats 8000000 in
/-- **`batch_map` of a small frame refines the spec's page-map decode and perform**
(`frame_map_rel` without the restart and `check_vspace`). -/
theorem batch_map_small_rel [PlainStore st] {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsFrameHyps st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPVa : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    {ptr rt fa fv : U64} {dev mp ep : Bool} (hep : mp = true → ep = false)
    (hfw : CapWf (.Frame ptr .Small rt dev mp ep fa fv)) (hfe : EncWf (.Frame ptr .Small rt dev mp ep fa fv))
    (hfcv : CapValid th (.Frame ptr .Small rt dev mp ep fa fv))
    (hfm : mp = true → fa ≠ 0#u64) (hfu : mp = true → UserV fv)
    (hpa : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub ptr layout.PPTR_BASE)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame ptr .Small rt dev mp ep fa fv))
    {p1 as1 : U64} (hp1 : p1 ∈ L4) (has1 : as1 ≠ 0#u64) (has2 : as1.val < 2 ^ 20)
    (hf : ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) as1.bv) σ = ({(.ok p1.bv, σ)}, False))
    (op depth a1 cr a2 : U64) (dd : Bool) (cn dcn : capability.Cap) (a0 : U64) :
    vspace.batch_map st ar s a (cslotAddr (pc.bv, idx)) ⟨p1, as1, op, depth, a1, cr, a2, dd, cn, dcn⟩ a0 ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ MapErrRel e e' ∧
        ExceptT.run (Fl4Spec.decodePageInvocation (Z := Unit) Fl4Spec.fbPageMapLabel [a0.bv, a1.bv, a2.bv] (pc.bv, idx)
        (.pageCap dev ptr.bv (vmRightsOf rt) (if mp then .vmVSpaceMap else .vmNoMap) .x64SmallPage
          (if mp then some (fa.bv, fv.bv) else none)) [(.archObjectCap (.pml4Cap p1.bv (some as1.bv)), (pc.bv, idx))]) σ = ({(.error e', σ)}, False) ∧ res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧ ∃ iv σ', ExceptT.run (Fl4Spec.decodePageInvocation (Z := Unit) Fl4Spec.fbPageMapLabel [a0.bv, a1.bv, a2.bv] (pc.bv, idx)
        (.pageCap dev ptr.bv (vmRightsOf rt) (if mp then .vmVSpaceMap else .vmNoMap) .x64SmallPage
          (if mp then some (fa.bv, fv.bv) else none)) [(.archObjectCap (.pml4Cap p1.bv (some as1.bv)), (pc.bv, idx))]) σ = ({(.ok iv, σ)}, False) ∧
        MapSpecN σ iv σ' ∧ StateRel th (L.mem res.2.1) σ' ∧ SlotsValid th (L.mem res.2.1) ∧
        VsRel P (L.mem res.2.1) (L.ksb res.2.1) σ' ∧ PtRel L4 L3 L2 L1 (L.mem res.2.1) σ' ∧ SR res.2.1 res.2.2 σ' ∧
        SlotFoot th (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) ∧
        VsLike (capV (L.mem res.2.1) (cslotAddr (pc.bv, idx))) (frameCapOf ⟨ptr, .Small, rt, dev, mp, ep, fa, fv⟩) ∧
        KFoot σ σ' ∧ FbKeep σ σ' ∧ CapPage σ σ' (pc.bv, idx) ∧
        MapLeafF (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) (.Frame ptr .Small rt dev mp ep fa fv) σ σ') ⦄ := by
  have hPV : ∀ b, PtW L1 b → ¬ VsWrite P (L.ksb s) b := fun b ⟨q, hq, i, hi, e⟩ =>
    hPVa b ⟨q, Or.inr (Or.inr (Or.inr hq)), i, hi, e⟩
  have hl := fb_label
  generalize hDec : ExceptT.run (Fl4Spec.decodePageInvocation (Z := Unit) Fl4Spec.fbPageMapLabel [a0.bv, a1.bv, a2.bv] (pc.bv, idx)
        (.pageCap dev ptr.bv (vmRightsOf rt) (if mp then .vmVSpaceMap else .vmNoMap) .x64SmallPage
          (if mp then some (fa.bv, fv.bv) else none)) [(.archObjectCap (.pml4Cap p1.bv (some as1.bv)), (pc.bv, idx))]) σ = D
  unfold vspace.batch_map
  rw [slot_cap_eq, hcap]
  simp only [bind_ok, vspace.as_frame]
  cases mp
  · simp only [Bool.false_eq_true, ↓reduceIte, lift, bind_ok, capability.FrameSize.bits, shl12]
    simp only [Bool.false_eq_true, ↓reduceIte] at hDec
    have hdec0 := decodeMap_unmapped hl a0.bv a1.bv a2.bv [] (pc.bv, idx) dev ptr.bv
      (vmRightsOf rt) .vmNoMap p1.bv as1.bv (pc.bv, idx) [] σ
    by_cases hv1 : a0 > fl4_abi.consts.USER_TOP
    · simp only [hv1, ↓reduceIte, error.invalid_arg, bind_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 0, rfl,
        Or.inl (Or.inl (show SysErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) from rfl)), ?_, rfl, rfl⟩)
      rw [← hDec, hdec0]
      exact runE_bind_err (by rw [runE_whenE_true (Or.inl ((gt_top a0).2 hv1))]; rfl)
    · by_cases hv2 : core.num.U64.wrapping_add a0 4096#u64 > fl4_abi.consts.USER_TOP
      · simp only [hv1, hv2, ↓reduceIte, error.invalid_arg, bind_ok]
        refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 0, rfl,
          Or.inl (Or.inl (show SysErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) from rfl)), ?_, rfl, rfl⟩)
        rw [← hDec, hdec0]
        exact runE_bind_err (by rw [runE_whenE_true (Or.inr (by rw [← add4096]; exact (gt_top _).2 hv2))]; rfl)
      · simp only [hv1, hv2, ↓reduceIte]
        have hdec : D = ExceptT.run (mapTail p1.bv as1.bv dev ptr.bv (vmRightsOf rt) a0.bv a1.bv a2.bv (pc.bv, idx)) σ := by
          rw [← hDec, hdec0, runE_bind_ok (runE_whenE_false ?_ _ σ)]
          rintro (h | h)
          · exact hv1 ((gt_top a0).1 h)
          · rw [← add4096] at h; exact hv2 ((gt_top _).1 h)
        have hva : a0.val < 2 ^ 48 := by
          have := (show ¬ a0 > fl4_abi.consts.USER_TOP from hv1)
          rw [gt_iff_val] at this
          have hU : fl4_abi.consts.USER_TOP.val = 140737488355327 := by unfold fl4_abi.consts.USER_TOP; rfl
          omega
        have hvU : UserV a0 := userV_of_not_gt hv1
        bmap_tail
  · have hep' := hep rfl
    subst hep'
    have hfa := hfm rfl
    have hfa' : (fa != 0#u64) = true := by simp [hfa]
    simp only [↓reduceIte, Bool.false_eq_true, lift, bind_ok, hfa', capability.FrameSize.bits, shl12]
    simp only [↓reduceIte] at hDec
    have hdec0 := decodeMap_mapped hl a0.bv a1.bv a2.bv [] (pc.bv, idx) dev ptr.bv
      (vmRightsOf rt) .vmVSpaceMap fa.bv fv.bv p1.bv as1.bv (pc.bv, idx) [] σ
    by_cases hfa1 : fa = as1
    · have : (fa != as1) = false := by simp [hfa1]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      by_cases hfv : fv = a0
      · have : (fv != a0) = false := by simp [hfv]
        simp only [this, Bool.false_eq_true, ↓reduceIte]
        have hdec : D = ExceptT.run (mapTail p1.bv as1.bv dev ptr.bv (vmRightsOf rt) a0.bv a1.bv a2.bv (pc.bv, idx)) σ := by
          rw [← hDec, hdec0, runE_bind_ok (runE_whenE_false (by simp [hfa1]) _ σ),
            runE_bind_ok (runE_whenE_false (by simp) _ σ), runE_bind_ok (runE_whenE_false (by simp [hfv]) _ σ)]
        have hva : a0.val < 2 ^ 48 := hfv ▸ hfe.2.2.2
        have hvU : UserV a0 := hfv ▸ hfu rfl
        bmap_tail
      · have : (fv != a0) = true := by simp [hfv]
        simp only [this, ↓reduceIte, error.invalid_arg, bind_ok]
        refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 0, rfl,
          Or.inl (Or.inl (show SysErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) from rfl)), ?_, rfl, rfl⟩)
        rw [← hDec, hdec0, runE_bind_ok (runE_whenE_false (by simp [hfa1]) _ σ),
          runE_bind_ok (runE_whenE_false (by simp) _ σ)]
        exact runE_bind_err (by rw [runE_whenE_true (show fv.bv ≠ a0.bv from fun h => hfv (eq_of_bv h))]; rfl)
    · have : (fa != as1) = true := by simp [hfa1]
      simp only [this, ↓reduceIte, error.invalid_cap, bind_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 1, rfl, Or.inl (Or.inr ⟨1#u64, rfl, rfl⟩), ?_, rfl, rfl⟩)
      rw [← hDec, hdec0]
      exact runE_bind_err (by rw [runE_whenE_true (show fa.bv ≠ as1.bv from fun h => hfa1 (eq_of_bv h))]; rfl)

set_option maxHeartbeats 8000000 in
/-- **`batch_map` of a large frame refines the spec's page-map decode and perform**
(`frame_map_large_rel` without the restart and `check_vspace`). -/
theorem batch_map_large_rel [PlainStore st] {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsFrameHypsL st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPVa : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    {ptr rt fa fv : U64} {dev mp ep : Bool} (hep : mp = true → ep = false)
    (hfw : CapWf (.Frame ptr .Large rt dev mp ep fa fv)) (hfe : EncWf (.Frame ptr .Large rt dev mp ep fa fv))
    (hfcv : CapValid th (.Frame ptr .Large rt dev mp ep fa fv))
    (hfm : mp = true → fa ≠ 0#u64) (hfu : mp = true → UserV fv)
    (hpa : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE &&& 4503599625273344#u64) =
      core.num.U64.wrapping_sub ptr layout.PPTR_BASE)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame ptr .Large rt dev mp ep fa fv))
    {p1 as1 : U64} (hp1 : p1 ∈ L4) (has1 : as1 ≠ 0#u64) (has2 : as1.val < 2 ^ 20)
    (hf : ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) as1.bv) σ = ({(.ok p1.bv, σ)}, False))
    (op depth a1 cr a2 : U64) (dd : Bool) (cn dcn : capability.Cap) (a0 : U64) :
    vspace.batch_map st ar s a (cslotAddr (pc.bv, idx)) ⟨p1, as1, op, depth, a1, cr, a2, dd, cn, dcn⟩ a0 ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ MapErrRel e e' ∧
        ExceptT.run (Fl4Spec.decodePageInvocation (Z := Unit) Fl4Spec.fbPageMapLabel [a0.bv, a1.bv, a2.bv] (pc.bv, idx)
        (.pageCap dev ptr.bv (vmRightsOf rt) (if mp then .vmVSpaceMap else .vmNoMap) .x64LargePage
          (if mp then some (fa.bv, fv.bv) else none)) [(.archObjectCap (.pml4Cap p1.bv (some as1.bv)), (pc.bv, idx))]) σ = ({(.error e', σ)}, False) ∧ res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧ ∃ iv σ', ExceptT.run (Fl4Spec.decodePageInvocation (Z := Unit) Fl4Spec.fbPageMapLabel [a0.bv, a1.bv, a2.bv] (pc.bv, idx)
        (.pageCap dev ptr.bv (vmRightsOf rt) (if mp then .vmVSpaceMap else .vmNoMap) .x64LargePage
          (if mp then some (fa.bv, fv.bv) else none)) [(.archObjectCap (.pml4Cap p1.bv (some as1.bv)), (pc.bv, idx))]) σ = ({(.ok iv, σ)}, False) ∧
        MapSpecN σ iv σ' ∧ StateRel th (L.mem res.2.1) σ' ∧ SlotsValid th (L.mem res.2.1) ∧
        VsRel P (L.mem res.2.1) (L.ksb res.2.1) σ' ∧ PtRel L4 L3 L2 L1 (L.mem res.2.1) σ' ∧ SR res.2.1 res.2.2 σ' ∧
        SlotFoot th (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) ∧
        VsLike (capV (L.mem res.2.1) (cslotAddr (pc.bv, idx))) (frameCapOf ⟨ptr, .Large, rt, dev, mp, ep, fa, fv⟩) ∧
        KFoot σ σ' ∧ FbKeep σ σ' ∧ CapPage σ σ' (pc.bv, idx) ∧
        MapLeafF (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) (.Frame ptr .Large rt dev mp ep fa fv) σ σ') ⦄ := by
  have hPV := hPVa
  have hl := fb_label
  generalize hDec : ExceptT.run (Fl4Spec.decodePageInvocation (Z := Unit) Fl4Spec.fbPageMapLabel [a0.bv, a1.bv, a2.bv] (pc.bv, idx)
        (.pageCap dev ptr.bv (vmRightsOf rt) (if mp then .vmVSpaceMap else .vmNoMap) .x64LargePage
          (if mp then some (fa.bv, fv.bv) else none)) [(.archObjectCap (.pml4Cap p1.bv (some as1.bv)), (pc.bv, idx))]) σ = D
  unfold vspace.batch_map
  rw [slot_cap_eq, hcap]
  simp only [bind_ok, vspace.as_frame]
  cases mp
  · simp only [Bool.false_eq_true, ↓reduceIte, lift, bind_ok, capability.FrameSize.bits, shl21]
    simp only [Bool.false_eq_true, ↓reduceIte] at hDec
    have hdec0 := decodeMapL_unmapped hl a0.bv a1.bv a2.bv [] (pc.bv, idx) dev ptr.bv
      (vmRightsOf rt) .vmNoMap p1.bv as1.bv (pc.bv, idx) [] σ
    by_cases hv1 : a0 > fl4_abi.consts.USER_TOP
    · simp only [hv1, ↓reduceIte, error.invalid_arg, bind_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 0, rfl,
        Or.inl (Or.inl (show SysErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) from rfl)), ?_, rfl, rfl⟩)
      rw [← hDec, hdec0]
      exact runE_bind_err (by rw [runE_whenE_true (Or.inl ((gt_top a0).2 hv1))]; rfl)
    · by_cases hv2 : core.num.U64.wrapping_add a0 2097152#u64 > fl4_abi.consts.USER_TOP
      · simp only [hv1, hv2, ↓reduceIte, error.invalid_arg, bind_ok]
        refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 0, rfl,
          Or.inl (Or.inl (show SysErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) from rfl)), ?_, rfl, rfl⟩)
        rw [← hDec, hdec0]
        exact runE_bind_err (by rw [runE_whenE_true (Or.inr (by rw [← addL]; exact (gt_top _).2 hv2))]; rfl)
      · simp only [hv1, hv2, ↓reduceIte]
        have hdec : D = ExceptT.run (mapTailL p1.bv as1.bv dev ptr.bv (vmRightsOf rt) a0.bv a1.bv a2.bv (pc.bv, idx)) σ := by
          rw [← hDec, hdec0, runE_bind_ok (runE_whenE_false ?_ _ σ)]
          rintro (h | h)
          · exact hv1 ((gt_top a0).1 h)
          · rw [← addL] at h; exact hv2 ((gt_top _).1 h)
        have hva : a0.val < 2 ^ 48 := by
          have := (show ¬ a0 > fl4_abi.consts.USER_TOP from hv1)
          rw [gt_iff_val] at this
          have hU : fl4_abi.consts.USER_TOP.val = 140737488355327 := by unfold fl4_abi.consts.USER_TOP; rfl
          omega
        have hvU : UserV a0 := userV_of_not_gt hv1
        bmap_tail_L
  · have hep' := hep rfl
    subst hep'
    have hfa := hfm rfl
    have hfa' : (fa != 0#u64) = true := by simp [hfa]
    simp only [↓reduceIte, Bool.false_eq_true, lift, bind_ok, hfa', capability.FrameSize.bits, shl21]
    simp only [↓reduceIte] at hDec
    have hdec0 := decodeMapL_mapped hl a0.bv a1.bv a2.bv [] (pc.bv, idx) dev ptr.bv
      (vmRightsOf rt) .vmVSpaceMap fa.bv fv.bv p1.bv as1.bv (pc.bv, idx) [] σ
    by_cases hfa1 : fa = as1
    · have : (fa != as1) = false := by simp [hfa1]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      by_cases hfv : fv = a0
      · have : (fv != a0) = false := by simp [hfv]
        simp only [this, Bool.false_eq_true, ↓reduceIte]
        have hdec : D = ExceptT.run (mapTailL p1.bv as1.bv dev ptr.bv (vmRightsOf rt) a0.bv a1.bv a2.bv (pc.bv, idx)) σ := by
          rw [← hDec, hdec0, runE_bind_ok (runE_whenE_false (by simp [hfa1]) _ σ),
            runE_bind_ok (runE_whenE_false (by simp) _ σ), runE_bind_ok (runE_whenE_false (by simp [hfv]) _ σ)]
        have hva : a0.val < 2 ^ 48 := hfv ▸ hfe.2.2.2
        have hvU : UserV a0 := hfv ▸ hfu rfl
        bmap_tail_L
      · have : (fv != a0) = true := by simp [hfv]
        simp only [this, ↓reduceIte, error.invalid_arg, bind_ok]
        refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 0, rfl,
          Or.inl (Or.inl (show SysErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) from rfl)), ?_, rfl, rfl⟩)
        rw [← hDec, hdec0, runE_bind_ok (runE_whenE_false (by simp [hfa1]) _ σ),
          runE_bind_ok (runE_whenE_false (by simp) _ σ)]
        exact runE_bind_err (by rw [runE_whenE_true (show fv.bv ≠ a0.bv from fun h => hfv (eq_of_bv h))]; rfl)
    · have : (fa != as1) = true := by simp [hfa1]
      simp only [this, ↓reduceIte, error.invalid_cap, bind_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 1, rfl, Or.inl (Or.inr ⟨1#u64, rfl, rfl⟩), ?_, rfl, rfl⟩)
      rw [← hDec, hdec0]
      exact runE_bind_err (by rw [runE_whenE_true (show fa.bv ≠ as1.bv from fun h => hfa1 (eq_of_bv h))]; rfl)

set_option maxHeartbeats 8000000 in
/-- **`batch_map` of a huge frame refines the spec's page-map decode and perform**
(`frame_map_huge_rel` without the restart and `check_vspace`). -/
theorem batch_map_huge_rel [PlainStore st] {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsFrameHypsL st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPVa : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    {ptr rt fa fv : U64} {dev mp ep : Bool} (hep : mp = true → ep = false)
    (hfw : CapWf (.Frame ptr .Huge rt dev mp ep fa fv)) (hfe : EncWf (.Frame ptr .Huge rt dev mp ep fa fv))
    (hfcv : CapValid th (.Frame ptr .Huge rt dev mp ep fa fv))
    (hfm : mp = true → fa ≠ 0#u64) (hfu : mp = true → UserV fv)
    (hpa : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE &&& 4503598553628672#u64) =
      core.num.U64.wrapping_sub ptr layout.PPTR_BASE)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame ptr .Huge rt dev mp ep fa fv))
    {p1 as1 : U64} (hp1 : p1 ∈ L4) (has1 : as1 ≠ 0#u64) (has2 : as1.val < 2 ^ 20)
    (hf : ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) as1.bv) σ = ({(.ok p1.bv, σ)}, False))
    (op depth a1 cr a2 : U64) (dd : Bool) (cn dcn : capability.Cap) (a0 : U64) :
    vspace.batch_map st ar s a (cslotAddr (pc.bv, idx)) ⟨p1, as1, op, depth, a1, cr, a2, dd, cn, dcn⟩ a0 ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ MapErrRel e e' ∧
        ExceptT.run (Fl4Spec.decodePageInvocation (Z := Unit) Fl4Spec.fbPageMapLabel [a0.bv, a1.bv, a2.bv] (pc.bv, idx)
        (.pageCap dev ptr.bv (vmRightsOf rt) (if mp then .vmVSpaceMap else .vmNoMap) .x64HugePage
          (if mp then some (fa.bv, fv.bv) else none)) [(.archObjectCap (.pml4Cap p1.bv (some as1.bv)), (pc.bv, idx))]) σ = ({(.error e', σ)}, False) ∧ res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧ ∃ iv σ', ExceptT.run (Fl4Spec.decodePageInvocation (Z := Unit) Fl4Spec.fbPageMapLabel [a0.bv, a1.bv, a2.bv] (pc.bv, idx)
        (.pageCap dev ptr.bv (vmRightsOf rt) (if mp then .vmVSpaceMap else .vmNoMap) .x64HugePage
          (if mp then some (fa.bv, fv.bv) else none)) [(.archObjectCap (.pml4Cap p1.bv (some as1.bv)), (pc.bv, idx))]) σ = ({(.ok iv, σ)}, False) ∧
        MapSpecN σ iv σ' ∧ StateRel th (L.mem res.2.1) σ' ∧ SlotsValid th (L.mem res.2.1) ∧
        VsRel P (L.mem res.2.1) (L.ksb res.2.1) σ' ∧ PtRel L4 L3 L2 L1 (L.mem res.2.1) σ' ∧ SR res.2.1 res.2.2 σ' ∧
        SlotFoot th (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) ∧
        VsLike (capV (L.mem res.2.1) (cslotAddr (pc.bv, idx))) (frameCapOf ⟨ptr, .Huge, rt, dev, mp, ep, fa, fv⟩) ∧
        KFoot σ σ' ∧ FbKeep σ σ' ∧ CapPage σ σ' (pc.bv, idx) ∧
        MapLeafF (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) (.Frame ptr .Huge rt dev mp ep fa fv) σ σ') ⦄ := by
  have hPV := hPVa
  have hl := fb_label
  generalize hDec : ExceptT.run (Fl4Spec.decodePageInvocation (Z := Unit) Fl4Spec.fbPageMapLabel [a0.bv, a1.bv, a2.bv] (pc.bv, idx)
        (.pageCap dev ptr.bv (vmRightsOf rt) (if mp then .vmVSpaceMap else .vmNoMap) .x64HugePage
          (if mp then some (fa.bv, fv.bv) else none)) [(.archObjectCap (.pml4Cap p1.bv (some as1.bv)), (pc.bv, idx))]) σ = D
  unfold vspace.batch_map
  rw [slot_cap_eq, hcap]
  simp only [bind_ok, vspace.as_frame]
  cases mp
  · simp only [Bool.false_eq_true, ↓reduceIte, lift, bind_ok, capability.FrameSize.bits, shl30]
    simp only [Bool.false_eq_true, ↓reduceIte] at hDec
    have hdec0 := decodeMapH_unmapped hl a0.bv a1.bv a2.bv [] (pc.bv, idx) dev ptr.bv
      (vmRightsOf rt) .vmNoMap p1.bv as1.bv (pc.bv, idx) [] σ
    by_cases hv1 : a0 > fl4_abi.consts.USER_TOP
    · simp only [hv1, ↓reduceIte, error.invalid_arg, bind_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 0, rfl,
        Or.inl (Or.inl (show SysErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) from rfl)), ?_, rfl, rfl⟩)
      rw [← hDec, hdec0]
      exact runE_bind_err (by rw [runE_whenE_true (Or.inl ((gt_top a0).2 hv1))]; rfl)
    · by_cases hv2 : core.num.U64.wrapping_add a0 1073741824#u64 > fl4_abi.consts.USER_TOP
      · simp only [hv1, hv2, ↓reduceIte, error.invalid_arg, bind_ok]
        refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 0, rfl,
          Or.inl (Or.inl (show SysErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) from rfl)), ?_, rfl, rfl⟩)
        rw [← hDec, hdec0]
        exact runE_bind_err (by rw [runE_whenE_true (Or.inr (by rw [← addH]; exact (gt_top _).2 hv2))]; rfl)
      · simp only [hv1, hv2, ↓reduceIte]
        have hdec : D = ExceptT.run (mapTailH p1.bv as1.bv dev ptr.bv (vmRightsOf rt) a0.bv a1.bv a2.bv (pc.bv, idx)) σ := by
          rw [← hDec, hdec0, runE_bind_ok (runE_whenE_false ?_ _ σ)]
          rintro (h | h)
          · exact hv1 ((gt_top a0).1 h)
          · rw [← addH] at h; exact hv2 ((gt_top _).1 h)
        have hva : a0.val < 2 ^ 48 := by
          have := (show ¬ a0 > fl4_abi.consts.USER_TOP from hv1)
          rw [gt_iff_val] at this
          have hU : fl4_abi.consts.USER_TOP.val = 140737488355327 := by unfold fl4_abi.consts.USER_TOP; rfl
          omega
        have hvU : UserV a0 := userV_of_not_gt hv1
        bmap_tail_H
  · have hep' := hep rfl
    subst hep'
    have hfa := hfm rfl
    have hfa' : (fa != 0#u64) = true := by simp [hfa]
    simp only [↓reduceIte, Bool.false_eq_true, lift, bind_ok, hfa', capability.FrameSize.bits, shl30]
    simp only [↓reduceIte] at hDec
    have hdec0 := decodeMapH_mapped hl a0.bv a1.bv a2.bv [] (pc.bv, idx) dev ptr.bv
      (vmRightsOf rt) .vmVSpaceMap fa.bv fv.bv p1.bv as1.bv (pc.bv, idx) [] σ
    by_cases hfa1 : fa = as1
    · have : (fa != as1) = false := by simp [hfa1]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      by_cases hfv : fv = a0
      · have : (fv != a0) = false := by simp [hfv]
        simp only [this, Bool.false_eq_true, ↓reduceIte]
        have hdec : D = ExceptT.run (mapTailH p1.bv as1.bv dev ptr.bv (vmRightsOf rt) a0.bv a1.bv a2.bv (pc.bv, idx)) σ := by
          rw [← hDec, hdec0, runE_bind_ok (runE_whenE_false (by simp [hfa1]) _ σ),
            runE_bind_ok (runE_whenE_false (by simp) _ σ), runE_bind_ok (runE_whenE_false (by simp [hfv]) _ σ)]
        have hva : a0.val < 2 ^ 48 := hfv ▸ hfe.2.2.2
        have hvU : UserV a0 := hfv ▸ hfu rfl
        bmap_tail_H
      · have : (fv != a0) = true := by simp [hfv]
        simp only [this, ↓reduceIte, error.invalid_arg, bind_ok]
        refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 0, rfl,
          Or.inl (Or.inl (show SysErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) from rfl)), ?_, rfl, rfl⟩)
        rw [← hDec, hdec0, runE_bind_ok (runE_whenE_false (by simp [hfa1]) _ σ),
          runE_bind_ok (runE_whenE_false (by simp) _ σ)]
        exact runE_bind_err (by rw [runE_whenE_true (show fv.bv ≠ a0.bv from fun h => hfv (eq_of_bv h))]; rfl)
    · have : (fa != as1) = true := by simp [hfa1]
      simp only [this, ↓reduceIte, error.invalid_cap, bind_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 1, rfl, Or.inl (Or.inr ⟨1#u64, rfl, rfl⟩), ?_, rfl, rfl⟩)
      rw [← hDec, hdec0]
      exact runE_bind_err (by rw [runE_whenE_true (show fa.bv ≠ as1.bv from fun h => hfa1 (eq_of_bv h))]; rfl)

section Spec
open Fl4Spec

theorem fbMap_page_err {b : Fl4FrameBatchInvocation} {cte : CslotPtr} {vaddr : Data} {σ : State Unit}
    {dev : Bool} {p : ObjRef} {R : VMRights} {mt : VMMapType} {sz : VMPageSize} {m : Option (Asid × VSpaceRef)}
    (hg : getCap (Z := Unit) cte σ = ({(.archObjectCap (.pageCap dev p R mt sz m), σ)}, False))
    (hne : ¬ (m.isSome ∧ mt = .vmEptMap)) {e : SyscallError}
    (hd : ExceptT.run (decodePageInvocation (Z := Unit) fbPageMapLabel [vaddr, b.mapRights, b.attr] cte
      (.pageCap dev p R mt sz m) [(.archObjectCap (.pml4Cap b.vspace (some b.asid)), cte)]) σ =
      ({(.error e, σ)}, False)) :
    ExceptT.run (fbMap (Z := Unit) b cte vaddr) σ = ({(.error e, σ)}, False) := by
  unfold fbMap
  rw [run_bind_ok (run_liftE hg)]
  dsimp only
  rw [runE_bind_ok (runE_whenE_false hne _ σ)]
  exact runE_bind_err hd

theorem fbMap_page_ok {b : Fl4FrameBatchInvocation} {cte : CslotPtr} {vaddr : Data} {σ σ' : State Unit}
    {dev : Bool} {p : ObjRef} {R : VMRights} {mt : VMMapType} {sz : VMPageSize} {m : Option (Asid × VSpaceRef)}
    (hg : getCap (Z := Unit) cte σ = ({(.archObjectCap (.pageCap dev p R mt sz m), σ)}, False))
    (hne : ¬ (m.isSome ∧ mt = .vmEptMap)) {pi : PageInvocation}
    (hd : ExceptT.run (decodePageInvocation (Z := Unit) fbPageMapLabel [vaddr, b.mapRights, b.attr] cte
      (.pageCap dev p R mt sz m) [(.archObjectCap (.pml4Cap b.vspace (some b.asid)), cte)]) σ =
      ({(.ok (.invokePage pi), σ)}, False))
    (hm : (([] : List Data), σ') ∈ (performPageInvocation (Z := Unit) pi σ).1) :
    ((.ok (), σ') : Except SyscallError Unit × State Unit) ∈ (ExceptT.run (fbMap (Z := Unit) b cte vaddr) σ).1 := by
  unfold fbMap
  rw [run_bind_ok (run_liftE hg)]
  dsimp only
  rw [runE_bind_ok (runE_whenE_false hne _ σ), runE_bind_ok hd]
  exact mem_bindE_ok (mem_liftE (x := (([] : List Data), σ')) hm) (Set.mem_singleton _)

theorem fbMap_nonPage {b : Fl4FrameBatchInvocation} {cte : CslotPtr} {vaddr : Data} {σ : State Unit} {c : Cap}
    (hg : getCap (Z := Unit) cte σ = ({(c, σ)}, False))
    (hc : ∀ dev p R mt sz m, c ≠ .archObjectCap (.pageCap dev p R mt sz m)) :
    ExceptT.run (fbMap (Z := Unit) b cte vaddr) σ = ({(.error (.invalidCapability 0), σ)}, False) := by
  unfold fbMap
  rw [run_bind_ok (run_liftE hg)]
  split
  · rename_i dev p R mt sz m
    exact absurd rfl (hc dev p R mt sz m)
  · rfl

theorem fbMap_ept {b : Fl4FrameBatchInvocation} {cte : CslotPtr} {vaddr : Data} {σ : State Unit}
    {dev : Bool} {p : ObjRef} {R : VMRights} {sz : VMPageSize} {m : Asid × VSpaceRef}
    (hg : getCap (Z := Unit) cte σ = ({(.archObjectCap (.pageCap dev p R .vmEptMap sz (some m)), σ)}, False)) :
    ExceptT.run (fbMap (Z := Unit) b cte vaddr) σ = ({(.error (.invalidCapability 0), σ)}, False) := by
  unfold fbMap
  rw [run_bind_ok (run_liftE hg)]
  dsimp only
  exact runE_bind_err (by rw [runE_whenE_true (by simp)]; rfl)

end Spec

set_option maxHeartbeats 8000000 in
/-- **FL4's `batch_map` refines the spec's `fbMap`** (module docstring): at the slot `(pc, idx)`
holding `c`, the batch's root `p1` (in `L4`, `find_vspace_for_asid` naming it) and ASID `as1`. -/
theorem batch_map_rel [PlainStore st] {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsFrameHyps st A ar th P L4 L3 L2 L1 SR)
    (hHL : VsFrameHypsL st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPVa : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {c : capability.Cap} (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok c)
    (hok : ∀ p sz rt d m e fa fv, c = .Frame p sz rt d m e fa fv → VCapOK P L4 L3 L2 L1 c) (hnat : NativeCap c)
    {p1 as1 : U64} (hp1 : p1 ∈ L4) (has1 : as1 ≠ 0#u64) (has2 : as1.val < 2 ^ 20)
    (hf : ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) as1.bv) σ = ({(.ok p1.bv, σ)}, False))
    (op depth a1 cr a2 : U64) (dd : Bool) (cn dcn : capability.Cap) (a0 : U64)
    (b : Fl4Spec.Fl4FrameBatchInvocation) (hbv : b.vspace = p1.bv) (hba : b.asid = as1.bv)
    (hbm : b.mapRights = a1.bv) (hbat : b.attr = a2.bv) :
    vspace.batch_map st ar s a (cslotAddr (pc.bv, idx)) ⟨p1, as1, op, depth, a1, cr, a2, dd, cn, dcn⟩ a0 ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ MapErrRel e e' ∧
        ExceptT.run (Fl4Spec.fbMap (Z := Unit) b (pc.bv, idx) a0.bv) σ = ({(.error e', σ)}, False) ∧
        res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧ ∃ σ', ((.ok (), σ') : Except Fl4Spec.SyscallError Unit × Fl4Spec.State Unit) ∈
          (ExceptT.run (Fl4Spec.fbMap (Z := Unit) b (pc.bv, idx) a0.bv) σ).1 ∧
        (∃ pi, (([] : List Fl4Spec.Data), σ') ∈ (Fl4Spec.performPageInvocation (Z := Unit) pi σ).1) ∧
        StateRel th (L.mem res.2.1) σ' ∧ SlotsValid th (L.mem res.2.1) ∧
        VsRel P (L.mem res.2.1) (L.ksb res.2.1) σ' ∧ PtRel L4 L3 L2 L1 (L.mem res.2.1) σ' ∧ SR res.2.1 res.2.2 σ' ∧
        SlotFoot th (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) ∧
        VsLike (capV (L.mem res.2.1) (cslotAddr (pc.bv, idx))) c ∧ KFoot σ σ' ∧ FbKeep σ σ' ∧
        CapPage σ σ' (pc.bv, idx) ∧ MapLeafF (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) c σ σ' ∧
        ∃ p sz rt d m e fa fv, c = .Frame p sz rt d m e fa fv) ⦄ := by
  obtain ⟨cS, aS, hcS, hcaS, hgS⟩ := hSt.slot_cap (Z := Unit) (sl := (pc.bv, idx)) (p := pc) rfl
    (by simpa [hidx] using hpc)
  rw [hcap] at hcS; cases eq_of_ok_eq hcS
  rw [hcaS.abs] at hgS
  have hcw : CapWf c := hcaS.1
  have hce : EncWf c := by have h := hcap; rw [capAt_words] at h; exact decode_encWf h
  have hcv : CapValid th c := hSV.cnode pc r hpc (blVal 0 idx) (hidx ▸ blVal_lt idx) _
    (by rw [show slotAddr pc.bv (BitVec.ofNat 64 (blVal 0 idx)) = cslotAddr (pc.bv, idx) from
      (slotAddr_ofBl pc idx).symm]; exact hcap)
  cases c
  case Frame ptr sz rt dev mp ep fa fv =>
    by_cases hme : mp = true ∧ ep = true
    · obtain ⟨rfl, rfl⟩ := hme
      exact absurd hnat (by simp [NativeCap])
    have hep : mp = true → ep = false := fun h => by cases ep <;> simp_all
    obtain ⟨hfm, hpa, hfu⟩ := hok _ _ _ _ _ _ _ _ rfl
    have hgS' : Fl4Spec.getCap (Z := Unit) (pc.bv, idx) σ = ({(.archObjectCap (.pageCap dev ptr.bv (vmRightsOf rt)
        (if mp then .vmVSpaceMap else .vmNoMap) (frameSizeOf sz) (if mp then some (fa.bv, fv.bv) else none)), σ)},
        False) := by
      rw [hgS]; cases mp <;> simp [absCap, hep]
    have hne : ¬ ((if mp then some (fa.bv, fv.bv) else none).isSome ∧
        (if mp then Fl4Spec.VMMapType.vmVSpaceMap else .vmNoMap) = .vmEptMap) := by
      cases mp <;> simp
    have hlike : ∀ c', VsLike c' (frameCapOf ⟨ptr, sz, rt, dev, mp, ep, fa, fv⟩) →
        VsLike c' (.Frame ptr sz rt dev mp ep fa fv) := by
      rintro c' ⟨⟨h1, h2, h3, h4⟩, h5⟩
      refine ⟨⟨h1, h2, h3, ?_⟩, fun P L4 L3 L2 L1 h => h5 P L4 L3 L2 L1 h⟩
      rw [h4]; cases mp <;> simp [frameCapOf, vtF, hep]
    have post : ∀ res : core.result.Result Unit error.Exc × S × A,
        ((∃ e e', res.1 = .Err e ∧ MapErrRel e e' ∧
          ExceptT.run (Fl4Spec.decodePageInvocation (Z := Unit) Fl4Spec.fbPageMapLabel [a0.bv, a1.bv, a2.bv] (pc.bv, idx)
            (.pageCap dev ptr.bv (vmRightsOf rt) (if mp then .vmVSpaceMap else .vmNoMap) (frameSizeOf sz)
              (if mp then some (fa.bv, fv.bv) else none)) [(.archObjectCap (.pml4Cap p1.bv (some as1.bv)), (pc.bv, idx))]) σ =
            ({(.error e', σ)}, False) ∧ res.2.1 = s ∧ res.2.2 = a) ∨
        (res.1 = .Ok () ∧ ∃ iv σ', ExceptT.run (Fl4Spec.decodePageInvocation (Z := Unit) Fl4Spec.fbPageMapLabel
            [a0.bv, a1.bv, a2.bv] (pc.bv, idx)
            (.pageCap dev ptr.bv (vmRightsOf rt) (if mp then .vmVSpaceMap else .vmNoMap) (frameSizeOf sz)
              (if mp then some (fa.bv, fv.bv) else none)) [(.archObjectCap (.pml4Cap p1.bv (some as1.bv)), (pc.bv, idx))]) σ =
            ({(.ok iv, σ)}, False) ∧
          MapSpecN σ iv σ' ∧ StateRel th (L.mem res.2.1) σ' ∧ SlotsValid th (L.mem res.2.1) ∧
          VsRel P (L.mem res.2.1) (L.ksb res.2.1) σ' ∧ PtRel L4 L3 L2 L1 (L.mem res.2.1) σ' ∧ SR res.2.1 res.2.2 σ' ∧
          SlotFoot th (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) ∧
          VsLike (capV (L.mem res.2.1) (cslotAddr (pc.bv, idx))) (frameCapOf ⟨ptr, sz, rt, dev, mp, ep, fa, fv⟩) ∧
          KFoot σ σ' ∧ FbKeep σ σ' ∧ CapPage σ σ' (pc.bv, idx) ∧
          MapLeafF (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) (.Frame ptr sz rt dev mp ep fa fv) σ σ')) →
        ((∃ e e', res.1 = .Err e ∧ MapErrRel e e' ∧
          ExceptT.run (Fl4Spec.fbMap (Z := Unit) b (pc.bv, idx) a0.bv) σ = ({(.error e', σ)}, False) ∧
          res.2.1 = s ∧ res.2.2 = a) ∨
        (res.1 = .Ok () ∧ ∃ σ', ((.ok (), σ') : Except Fl4Spec.SyscallError Unit × Fl4Spec.State Unit) ∈
            (ExceptT.run (Fl4Spec.fbMap (Z := Unit) b (pc.bv, idx) a0.bv) σ).1 ∧
          (∃ pi, (([] : List Fl4Spec.Data), σ') ∈ (Fl4Spec.performPageInvocation (Z := Unit) pi σ).1) ∧
          StateRel th (L.mem res.2.1) σ' ∧ SlotsValid th (L.mem res.2.1) ∧
          VsRel P (L.mem res.2.1) (L.ksb res.2.1) σ' ∧ PtRel L4 L3 L2 L1 (L.mem res.2.1) σ' ∧ SR res.2.1 res.2.2 σ' ∧
          SlotFoot th (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) ∧
          VsLike (capV (L.mem res.2.1) (cslotAddr (pc.bv, idx))) (.Frame ptr sz rt dev mp ep fa fv) ∧
          KFoot σ σ' ∧ FbKeep σ σ' ∧ CapPage σ σ' (pc.bv, idx) ∧
          MapLeafF (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) (.Frame ptr sz rt dev mp ep fa fv) σ σ' ∧
          ∃ p' sz' rt' d' m' e' fa' fv', capability.Cap.Frame ptr sz rt dev mp ep fa fv =
            .Frame p' sz' rt' d' m' e' fa' fv')) := by
      have hb3 : [a0.bv, a1.bv, a2.bv] = [a0.bv, b.mapRights, b.attr] := by rw [hbm, hbat]
      have hb4 : (Fl4Spec.Cap.archObjectCap (.pml4Cap p1.bv (some as1.bv))) =
          .archObjectCap (.pml4Cap b.vspace (some b.asid)) := by rw [hbv, hba]
      rintro res (⟨e, e', h1, h2, h3, h4, h5⟩ | ⟨h1, iv, σ', h3, hms, h6⟩)
      · refine Or.inl ⟨e, e', h1, h2, fbMap_page_err hgS' hne ?_, h4, h5⟩
        rw [← hb3, ← hb4]; exact h3
      · cases iv with
        | invokePage pi =>
          obtain ⟨hm, -⟩ := hms
          refine Or.inr ⟨h1, σ', fbMap_page_ok hgS' hne (by rw [← hb3, ← hb4]; exact h3) hm, ⟨pi, hm⟩, ?_⟩
          obtain ⟨a1', a2', a3', a4', a5', a6', a7', a8', a9', a10', a11'⟩ := h6
          exact ⟨a1', a2', a3', a4', a5', a6', hlike _ a7', a8', a9', a10', a11', _, _, _, _, _, _, _, _, rfl⟩
        | _ => exact hms.elim
    cases sz
    · exact WP.spec_mono (batch_map_small_rel hH s a σ hPl hVP hD hPP hPS hPVa hPO hSt hSV hR hPt hS hep hcw hce hcv
        hfm hfu hpa hpc hidx hcap hp1 has1 has2 hf op depth a1 cr a2 dd cn dcn a0) post
    · exact WP.spec_mono (batch_map_large_rel hHL s a σ hPl hVP hD hPP hPS hPVa hPO hSt hSV hR hPt hS hep hcw hce hcv
        hfm hfu hpa hpc hidx hcap hp1 has1 has2 hf op depth a1 cr a2 dd cn dcn a0) post
    · exact WP.spec_mono (batch_map_huge_rel hHL s a σ hPl hVP hD hPP hPS hPVa hPO hSt hSV hR hPt hS hep hcw hce hcv
        hfm hfu hpa hpc hidx hcap hp1 has1 has2 hf op depth a1 cr a2 dd cn dcn a0) post
  all_goals
    unfold vspace.batch_map
    rw [slot_cap_eq, hcap]
    simp only [bind_ok, vspace.as_frame, error.invalid_cap]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 0, rfl, Or.inl (Or.inr ⟨0#u64, rfl, rfl⟩),
      fbMap_nonPage hgS (fun _ _ _ _ _ _ h => by simp [absCap] at h), rfl, rfl⟩)

end

end

end Fl4Proofs.P3.Vs
