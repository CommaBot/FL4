/-
P3 (DESIGN.md §9), VSpace: **PageTable `Unmap`, the spec side**: l4v's
`decode_page_table_invocation` with label `X64PageTableUnmap`,
`unmap_page_table`, and the clearing of the table in
`perform_page_table_invocation`.

* `ptDecodeUnmap_final`, `ptDecodeUnmap_notFinal`: the decode;
* `unmapPT_noVs`, `unmapPT_noSlot`, `unmapPT_other`, `unmapPT_match`:
  `unmap_page_table` for each result of the lookups;
* `flushTable_mem`: `flush_table` changes only the machine state;
* `clearPt_eq`: storing `InvalidPTE` in every slot of a page table.
-/
import Fl4Proofs.P3.VsPtMapRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

section Spec
open Fl4Spec

open Classical in
theorem ptDecodeUnmap_final {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PageTableUnmap)
    (args : List Data) (cte : CslotPtr) (p : ObjRef) (ma : Option (Asid × VSpaceRef)) (ex : List (Cap × CslotPtr))
    (σ : State Unit) (hf : isFinalCap' (Cap.archObjectCap (.pageTableCap p ma)) σ) :
    ExceptT.run (decodePageTableInvocation (Z := Unit) lbl args cte (.pageTableCap p ma) ex) σ =
      ({(.ok (.invokePageTable (.pageTableUnmap (.archObjectCap (.pageTableCap p ma)) cte)), σ)}, False) := by
  unfold decodePageTableInvocation
  dsimp only
  rw [if_neg (by rw [hl]; simp), if_pos hl,
    runE_bind_ok (runE_liftE (show isFinalCap (Z := Unit) _ σ = ({(decide (isFinalCap' _ σ), σ)}, False) from rfl))]
  rw [runE_bind_ok (runE_unlessE_true (by simpa using hf) _ σ)]
  rfl

open Classical in
theorem ptDecodeUnmap_notFinal {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PageTableUnmap)
    (args : List Data) (cte : CslotPtr) (p : ObjRef) (ma : Option (Asid × VSpaceRef)) (ex : List (Cap × CslotPtr))
    (σ : State Unit) (hf : ¬ isFinalCap' (Cap.archObjectCap (.pageTableCap p ma)) σ) :
    ExceptT.run (decodePageTableInvocation (Z := Unit) lbl args cte (.pageTableCap p ma) ex) σ =
      ({(.error .revokeFirst, σ)}, False) := by
  unfold decodePageTableInvocation
  dsimp only
  rw [if_neg (by rw [hl]; simp), if_pos hl,
    runE_bind_ok (runE_liftE (show isFinalCap (Z := Unit) _ σ = ({(decide (isFinalCap' _ σ), σ)}, False) from rfl))]
  exact runE_bind_err (by rw [runE_unlessE_false (by simpa using hf)]; rfl)

theorem catch_congr {α ε : Type} {m m' : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} {σ : State Unit}
    (hm : ExceptT.run m σ = ExceptT.run m' σ) : NonDetE.catch m h σ = NonDetE.catch m' h σ := by
  unfold NonDetE.catch NonDet.bind
  rw [hm]

theorem catch_liftE {α ε : Type} (n : NonDet (State Unit) α) (h : ε → NonDet (State Unit) α) (σ : State Unit) :
    NonDetE.catch (NonDetE.liftE n) h σ = n σ := by
  unfold NonDetE.catch NonDetE.liftE
  show NonDet.bind (NonDet.bind n (fun a => NonDet.pure (Except.ok a))) _ σ = n σ
  unfold NonDet.bind NonDet.pure
  ext x
  · simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, hy⟩
      simpa using hy ▸ hz
    · intro hx
      exact ⟨(.ok x.1, x.2), ⟨x, hx, rfl⟩, by simp⟩
  · simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro (h1 | ⟨y, ⟨z, hz, rfl⟩, hy⟩)
      · rcases h1 with h1 | ⟨_, _, h1⟩
        · exact h1
        · exact h1.elim
      · exact hy.elim
    · intro h1; exact Or.inl (Or.inl h1)

theorem unmapPT_noVs {asid : Asid} {v : VSpaceRef} {pt : ObjRef} {σ : State Unit} {e : LookupFailure}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.error e, σ)}, False)) :
    unmapPageTable (Z := Unit) asid v pt σ = ({((), σ)}, False) := by
  unfold unmapPageTable
  rw [catch_err (runE_bind_err hf)]
  rfl

theorem unmapPT_noSlot {asid : Asid} {v : VSpaceRef} {pt vs : ObjRef} {σ : State Unit} {e : LookupFailure}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok vs, σ)}, False))
    (hl : ExceptT.run (lookupPdSlot (Z := Unit) vs v) σ = ({(.error e, σ)}, False)) :
    unmapPageTable (Z := Unit) asid v pt σ = ({((), σ)}, False) := by
  unfold unmapPageTable
  rw [catch_err (by rw [runE_bind_ok hf]; exact runE_bind_err hl)]
  rfl

theorem unmapPT_other {asid : Asid} {v : VSpaceRef} {pt vs slot : ObjRef} {σ : State Unit} {pde : PDE}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok vs, σ)}, False))
    (hl : ExceptT.run (lookupPdSlot (Z := Unit) vs v) σ = ({(.ok slot, σ)}, False))
    (hg : getPde (Z := Unit) slot σ = ({(pde, σ)}, False))
    (hm : ∀ a b c, pde = .pageTablePDE a b c → addrFromPPtr pt ≠ a) :
    unmapPageTable (Z := Unit) asid v pt σ = ({((), σ)}, False) := by
  unfold unmapPageTable
  refine (catch_err (e := .invalidRoot) ?_).trans rfl
  rw [runE_bind_ok hf, runE_bind_ok hl, runE_bind_ok (runE_liftE hg)]
  cases pde with
  | pageTablePDE a b c => dsimp only; rw [if_neg (hm a b c rfl)]; exact runE_bind_err (runE_throw _ σ)
  | invalidPDE => exact runE_bind_err (runE_throw _ σ)
  | largePagePDE _ _ _ => exact runE_bind_err (runE_throw _ σ)

theorem unmapPT_match {asid : Asid} {v : VSpaceRef} {pt vs slot : ObjRef} {σ : State Unit}
    {ta : TableAttrs} {tr : CapRights}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok vs, σ)}, False))
    (hl : ExceptT.run (lookupPdSlot (Z := Unit) vs v) σ = ({(.ok slot, σ)}, False))
    (hg : getPde (Z := Unit) slot σ = ({(.pageTablePDE (addrFromPPtr pt) ta tr, σ)}, False)) :
    unmapPageTable (Z := Unit) asid v pt σ = (flushTable (Z := Unit) vs v pt asid >>= fun _ =>
      storePde slot .invalidPDE >>= fun _ => invalidatePageStructureCacheAsid (addrFromPPtr vs) asid) σ := by
  unfold unmapPageTable
  refine (catch_congr (m' := NonDetE.liftE (flushTable (Z := Unit) vs v pt asid >>= fun _ =>
      storePde slot .invalidPDE >>= fun _ => invalidatePageStructureCacheAsid (addrFromPPtr vs) asid)) ?_).trans
    (catch_liftE _ _ _)
  rw [runE_bind_ok hf, runE_bind_ok hl, runE_bind_ok (runE_liftE hg)]
  dsimp only
  rw [if_pos rfl, runE_bind_ok (runE_ret _ σ)]

/-- `mapM_x` of machine operations changes only the machine state. -/
theorem mapMx_mem {β γ : Type} (g : γ → NonDet (State Unit) β)
    (hg : ∀ x (σ σ' : State Unit) r, (r, σ') ∈ (g x σ).1 → ∃ ms, σ' = { σ with machineState := ms }) :
    ∀ (xs : List γ) (σ σ' : State Unit) (r : Unit), (r, σ') ∈ (NonDet.mapMx g xs σ).1 →
      ∃ ms, σ' = { σ with machineState := ms } := by
  intro xs
  induction xs with
  | nil =>
    intro σ σ' r h
    simp only [NonDet.mapMx, NonDet.pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
    exact ⟨σ.machineState, by rw [h.2]⟩
  | cons x xs ih =>
    intro σ σ' r h
    simp only [NonDet.mapMx] at h
    rw [show NonDet.bind (g x) (fun _ => NonDet.mapMx g xs) σ = ((g x) >>= fun _ => NonDet.mapMx g xs) σ from rfl,
      nd_bind_apply'] at h
    obtain ⟨y, hy, h2⟩ := h
    obtain ⟨ms1, h1⟩ := hg x σ y.2 y.1 hy
    obtain ⟨ms2, h3⟩ := ih y.2 σ' r h2
    exact ⟨ms2, by rw [h3, h1]⟩

/-- **`flush_table` changes only the machine state.** -/
theorem flushTable_mem {vs : ObjRef} {v : VSpaceRef} {pt : ObjRef} {asid : Asid} {σ σ' : State Unit}
    (h : ((), σ') ∈ (flushTable (Z := Unit) vs v pt asid σ).1) : ∃ ms, σ' = { σ with machineState := ms } := by
  unfold flushTable at h
  rw [nd_bind_apply'] at h
  obtain ⟨y, hy, h⟩ := h
  simp only [NonDet.assert] at hy
  · obtain ⟨-, rfl⟩ := hy
    rw [nd_bind_apply'] at h
    obtain ⟨z, hz, h⟩ := h
    unfold getPt at hz
    rw [nd_bind_apply'] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have hw' : w.2 = σ := by
      change w ∈ (getObject (Z := Unit) pt σ).1 at hw
      cases hk : σ.kheap pt with
      | some o => rw [getObject_eq hk] at hw; simp at hw; rw [hw]
      | none =>
        simp [getObject, NonDet.getsThe, readObject, hk, NonDet.assertOpt, nd_bind_apply', NonDet.gets,
          NonDet.fail] at hw
    have hz' : z.2 = w.2 := by
      generalize w.1 = o at hz
      cases o with
      | archObj ao => cases ao <;> simp_all [NonDet.fail, pure, NonDet.pure]
      | _ => simp_all [NonDet.fail]
    unfold NonDet.forMx at h
    refine mapMx_mem _ ?_ _ z.2 σ' () h |>.imp fun ms hms => by rw [hms, hz', hw']
    intro x σ0 σ1 r hx
    rw [nd_pure_bind'] at hx
    generalize z.1 x = pte at hx
    cases pte with
    | invalidPTE =>
      simp only [pure, NonDet.pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      exact ⟨σ0.machineState, by rw [hx.2]⟩
    | smallPagePTE _ _ _ => exact doMachineOp_mem hx

theorem updK_self {σ : State Unit} {p : ObjRef} {o : KernelObject} (hk : σ.kheap p = some o) : updK σ p o = σ := by
  have : Function.update σ.kheap p (some o) = σ.kheap := by
    rw [Function.update_eq_self_iff]; exact hk.symm
  unfold updK; rw [this]

theorem updK_updK (σ : State Unit) (p : ObjRef) (o o' : KernelObject) : updK (updK σ p o) p o' = updK σ p o' := by
  unfold updK; simp [Function.update_idem]

theorem ucast_ofNat {j : Nat} (hj : j < 512) (k : BitVec 9) :
    (ucast 9 (BitVec.ofNat 64 j) : BitVec 9) = k ↔ k.toNat = j := by
  constructor
  · rintro rfl; simp [ucast, BitVec.toNat_setWidth]; omega
  · intro h; apply BitVec.eq_of_toNat_eq; simp [ucast, BitVec.toNat_setWidth, h]; omega

/-- Storing `InvalidPTE` in the slots `js` of a page table. -/
theorem clearPt_gen {q : U64} (hq : q.val % 4096 = 0) :
    ∀ (js : List Nat), (∀ j ∈ js, j < 512) → ∀ (σ : State Unit) (f : BitVec 9 → PTE),
      σ.kheap q.bv = some (.archObj (.pageTable f)) →
      NonDet.mapMx (fun slot => storePte (Z := Unit) slot .invalidPTE)
        (js.map fun j => q.bv + (BitVec.ofNat 64 j <<< wordSizeBits)) σ =
      ({((), updK σ q.bv (.archObj (.pageTable fun k => if k.toNat ∈ js then .invalidPTE else f k)))}, False) := by
  intro js
  induction js with
  | nil =>
    intro _ σ f hk
    simp only [List.map_nil, NonDet.mapMx, List.not_mem_nil, if_false]
    rw [updK_self hk]; rfl
  | cons j js ih =>
    intro hjs σ f hk
    have hj : j < 512 := hjs j (by simp)
    set j' : U64 := ⟨BitVec.ofNat 64 j⟩
    have hj' : j'.val = j := by
      show (BitVec.ofNat 64 j).toNat = j
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [List.map_cons, NonDet.mapMx]
    rw [show NonDet.bind (storePte (Z := Unit) (q.bv + (BitVec.ofNat 64 j <<< wordSizeBits)) .invalidPTE)
        (fun _ => NonDet.mapMx (fun slot => storePte (Z := Unit) slot .invalidPTE)
          (js.map fun j => q.bv + (BitVec.ofNat 64 j <<< wordSizeBits))) σ =
        (storePte (Z := Unit) (q.bv + (j'.bv <<< wordSizeBits)) .invalidPTE >>= fun _ =>
          NonDet.mapMx (fun slot => storePte (Z := Unit) slot .invalidPTE)
          (js.map fun j => q.bv + (BitVec.ofNat 64 j <<< wordSizeBits))) σ from rfl]
    rw [nd_bind_one (storePte_at hq hk (by omega) .invalidPTE)]
    rw [ih (fun j h => hjs j (by simp [h])) _ (Function.update f (ucast 9 j'.bv) .invalidPTE) (by simp [updK]),
      updK_updK]
    have hF : (fun k : BitVec 9 => if k.toNat ∈ js then PTE.invalidPTE else Function.update f (ucast 9 j'.bv) .invalidPTE k) =
        (fun k => if k.toNat ∈ j :: js then .invalidPTE else f k) := by
      funext k
      by_cases h1 : k.toNat ∈ js
      · simp [h1]
      · by_cases h2 : k.toNat = j
        · have : (ucast 9 j'.bv : BitVec 9) = k := (ucast_ofNat hj k).2 h2
          simp [h1, h2, this]
        · have : (ucast 9 j'.bv : BitVec 9) ≠ k := fun h => h2 ((ucast_ofNat hj k).1 h)
          simp [h1, h2, Function.update_of_ne (Ne.symm this)]
    rw [hF]

theorem slots_eq {q : U64} (hq : q.val % 4096 = 0) :
    uptoEnumStep q.bv (q.bv + (1 : BitVec 64) <<< wordSizeBits) (q.bv + (1 : BitVec 64) <<< ptBits - 1) =
      (List.range 512).map (fun j => q.bv + (BitVec.ofNat 64 j <<< wordSizeBits)) := by
  have hf := tbl_fit hq
  have hqv : q.bv.toNat = q.val := rfl
  unfold uptoEnumStep uptoEnum
  have e1 : ((1 : BitVec 64) <<< ptBits) = 4096#64 := by decide
  have e2 : ((1 : BitVec 64) <<< wordSizeBits) = 8#64 := by decide
  simp only [e1, e2]
  have h1 : ¬ (q.bv + 4096#64 - 1 < q.bv) := by
    rw [BitVec.lt_def]; bv_omega
  rw [if_neg h1]
  have h2 : q.bv + 4096#64 - 1 - q.bv = 4095#64 := by bv_omega
  have h3 : (q.bv + 8#64 - q.bv) = 8#64 := by bv_omega
  rw [h2, h3, show (4095#64 : BitVec 64) / 8#64 = 511#64 by decide, List.map_map]
  rw [show (511#64).toNat + 1 - (0 : BitVec 64).toNat = 512 by decide, List.range_eq_range']
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_apply, wordSizeBits]
  rw [BitVec.shiftLeft_eq_mul_twoPow, show BitVec.twoPow 64 3 = 8#64 by decide]

theorem clearPt_eq {q : U64} (hq : q.val % 4096 = 0) {σ : State Unit} {f : BitVec 9 → PTE}
    (hk : σ.kheap q.bv = some (.archObj (.pageTable f))) :
    NonDet.mapMx (fun slot => storePte (Z := Unit) slot .invalidPTE)
      (uptoEnumStep q.bv (q.bv + (1 : BitVec 64) <<< wordSizeBits) (q.bv + (1 : BitVec 64) <<< ptBits - 1)) σ =
      ({((), updK σ q.bv (.archObj (.pageTable fun _ => .invalidPTE)))}, False) := by
  rw [slots_eq hq, clearPt_gen hq _ (fun j h => List.mem_range.1 h) σ f hk]
  have : (fun k : BitVec 9 => if k.toNat ∈ List.range 512 then PTE.invalidPTE else f k) = fun _ => .invalidPTE := by
    funext k
    have : k.toNat < 512 := k.isLt
    simp [List.mem_range, this]
  rw [this]

/-- The spec's PageTable Unmap perform, for a mapped table. -/
theorem performPtUnmap_mem {q : U64} (hq : q.val % 4096 = 0) {asid : Asid} {va : VSpaceRef}
    {pc : ObjRef} {idx : List Bool} {r : Nat} {cs : CnodeContents} {ma : Option (Asid × VSpaceRef)}
    {σ1 σu : State Unit}
    (hnu : ¬ (unmapPageTable (Z := Unit) asid va q.bv σ1).2)
    (hall : ∀ x σ, (x, σ) ∈ (unmapPageTable (Z := Unit) asid va q.bv σ1).1 →
      σ.kheap q.bv = σ1.kheap q.bv ∧ σ.kheap pc = σ1.kheap pc)
    (hu : ((), σu) ∈ (unmapPageTable (Z := Unit) asid va q.bv σ1).1) {f : BitVec 9 → PTE}
    (hkp : σ1.kheap q.bv = some (.archObj (.pageTable f))) (hkc : σ1.kheap pc = some (.cnode r cs))
    (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r) (hcs : cs idx = some (.archObjectCap (.pageTableCap q.bv ma))) :
    ((), setCnodeSlot (updK σu q.bv (.archObj (.pageTable fun _ => .invalidPTE))) pc r cs idx
        (.archObjectCap (.pageTableCap q.bv none))) ∈
      (performPageTableInvocation (Z := Unit)
        (.pageTableUnmap (.archObjectCap (.pageTableCap q.bv (some (asid, va)))) (pc, idx)) σ1).1 ∧
    ¬ (performPageTableInvocation (Z := Unit)
        (.pageTableUnmap (.archObjectCap (.pageTableCap q.bv (some (asid, va)))) (pc, idx)) σ1).2 := by
  have hqc : q.bv ≠ pc := kheap_ne hkp hkc (fun _ h1 h2 => by subst h1; cases h2)
  have tailCap : ∀ σ : State Unit, σ.kheap pc = some (.cnode r cs) →
      (NonDet.liftM Cap.theArchCap (getCap (Z := Unit) (pc, idx)) >>= fun cap =>
        setCap (Cap.archObjectCap (updateMapData cap none none)) (pc, idx)) σ =
      ({((), setCnodeSlot σ pc r cs idx (.archObjectCap (.pageTableCap q.bv none)))}, False) := by
    intro σ hk
    rw [nd_bind_one (by unfold NonDet.liftM; rw [nd_bind_one' (getCap_cnode hk hwf hcs)]; rfl)]
    exact setCap_cnode _ hk hwf hidx
  have hkc' : ∀ σ : State Unit, σ.kheap pc = σ1.kheap pc →
      (updK σ q.bv (.archObj (.pageTable fun _ => .invalidPTE))).kheap pc = some (.cnode r cs) := by
    intro σ h2; simp [updK, Ne.symm hqc, h2, hkc]
  unfold performPageTableInvocation
  dsimp only
  rw [nd_bind_apply']
  refine ⟨⟨((), σu), hu, ?_⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := hall _ _ hu
    rw [nd_pure_bind', nd_pure_bind', nd_bind_one (clearPt_eq hq (h1.trans hkp)), tailCap _ (hkc' _ h2)]
    rfl
  · rintro (h | ⟨y, hy, h⟩)
    · exact hnu h
    · obtain ⟨h1, h2⟩ := hall _ _ hy
      rw [nd_pure_bind', nd_pure_bind', nd_bind_one (clearPt_eq hq (h1.trans hkp)), tailCap _ (hkc' _ h2)] at h
      exact h

end Spec

end

end Fl4Proofs.P3.Vs
