/-
P3 (line mmuAD, gen 42b4): **ASIDPool `Assign` of an EPT root, the decode / perform relation** — the nested arm of
FL4's `vspace::decode` on an ASID-pool cap with label `X86ASIDPoolAssign` (vspace.rs l. 1217-1250: the first extra
cap `Ept { ptr, level: 0, mapped: false }`, `vroot = ptr | 1`, the cap rewritten `Ept { ptr, 0, mapped: true, asid,
vaddr: 0 }`, the pool word `ptr | 1`) against the extension spec's `decodeEptAsidPoolAssign` (Ext/VirtEptInv: the
ported decoder's checks, returning `.poolAssign`) followed by `setThreadState cur Restart` and
`performEptInvocation (.poolAssign …)` (`r ||| 1` stored in the pool).

* Spec: `eptAssign_prefix` / `eptAssign_noPool` / `eptAssign_wrong` / `eptAssign_full` / `eptAssign_mem` (the
  decoder's errors and its outcome for each free offset, as P3/VsAssign's `assignBody_*` for the native decoder),
  **`performEptAssign_eq`** (the perform's single outcome), `EptAssignSpec` (restart, then perform).
* FL4: `decode_loop2_eq` (the nested arm's free-entry search is the native arm's loop, `decode_loop1_spec`).
* **`assign_rel_ept`**: P3/VsAssignRel's `assign_rel` for the nested arm (same hypotheses `VsInvHyps`, with
  `hcx : … = ok (.Ept ptr1 0 false asid0 va0)` and `ptr1` even): either an error related to the spec decoder's,
  states unchanged, or success with the spec decoder's outcome `.poolAssign asid ptr (pc, idx)` (no failure), the
  single outcome `σ'` of restart + perform, `StateRel` / `SlotsValid` / `VsRel` / `SR` after, the slot footprint
  (`SlotFoot`, the new cap `Ept ptr1 0 true asid 0`), `KFoot`, the pool-word footprint (`ptr1 ||| 1`) and
  **`AssignFE`** (the spec side: pool entry `lo` written `some (ptr1 ||| 1)`, every other arch object and the ASID
  table kept).

No named premise; the spec is not touched. No `sorry`; only the three standard axioms.
-/
import Fl4Proofs.P3.VsAssignRel
import Fl4Proofs.P3.ScCallPopRef
import Fl4Spec.Ext.VirtEptInv
import Fl4Proofs.P3.ScCallCut
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

section Spec
open Fl4Spec

theorem eptAssign_prefix (p base : ObjRef) (sl : CslotPtr) (σ : State Unit) :
    ExceptT.run (decodeEptAsidPoolAssign (Z := Unit) p base sl) σ = ExceptT.run (do
      NonDetE.whenE (σ.archState.x64AsidTable (asidHighBitsOf base) = none) <|
        NonDetE.throwError (.failedLookup false .invalidRoot)
      NonDetE.whenE (p ≠ the (σ.archState.x64AsidTable (asidHighBitsOf base))) <|
        NonDetE.throwError (.invalidCapability 0)
      let pool ← NonDetE.liftE <| getAsidPool p
      let freeSet ← NonDetE.returnOk ((dom pool)ᶜ ∩ {x | ucast asidRepLen x + base ≠ 0})
      NonDetE.whenE (freeSet = ∅) <| NonDetE.throwError .deleteFirst
      let offset ← NonDetE.liftE <| selectExt (fun _ => freeAsidPoolSelect pool base) freeSet
      NonDetE.returnOk (ε := SyscallError) <| EptInvocation.poolAssign (ucast asidRepLen offset + base) p sl) σ := by
  unfold decodeEptAsidPoolAssign
  rw [runE_bind_ok (runE_liftE (show NonDet.gets _ σ = ({(σ.archState.x64AsidTable, σ)}, False) from rfl)),
    runE_bind_ok (runE_ret _ σ)]

theorem eptAssign_noPool {p base : ObjRef} {sl : CslotPtr} {σ : State Unit}
    (ht : σ.archState.x64AsidTable (asidHighBitsOf base) = none) :
    ExceptT.run (decodeEptAsidPoolAssign (Z := Unit) p base sl) σ =
      ({(.error (.failedLookup false .invalidRoot), σ)}, False) := by
  rw [eptAssign_prefix, ht]
  exact runE_bind_err (by rw [runE_whenE_true rfl]; exact runE_throw _ σ)

theorem eptAssign_wrong {p q base : ObjRef} {sl : CslotPtr} {σ : State Unit}
    (ht : σ.archState.x64AsidTable (asidHighBitsOf base) = some q) (hq : p ≠ q) :
    ExceptT.run (decodeEptAsidPoolAssign (Z := Unit) p base sl) σ = ({(.error (.invalidCapability 0), σ)}, False) := by
  rw [eptAssign_prefix, ht, runE_bind_ok (runE_whenE_false (by simp) _ σ)]
  exact runE_bind_err (by rw [runE_whenE_true (show p ≠ Fl4Spec.the (some q) from hq)]; exact runE_throw _ σ)

theorem eptAssign_pool {p base : ObjRef} {sl : CslotPtr} {σ : State Unit}
    (ht : σ.archState.x64AsidTable (asidHighBitsOf base) = some p) {f : AsidLowIndex → Option ObjRef}
    (hk : σ.kheap p = some (.archObj (.asidPool f))) :
    ExceptT.run (decodeEptAsidPoolAssign (Z := Unit) p base sl) σ = ExceptT.run (do
      NonDetE.whenE (freeSet f base = ∅) <| NonDetE.throwError .deleteFirst
      let offset ← NonDetE.liftE <| selectExt (fun _ => freeAsidPoolSelect f base) (freeSet f base)
      NonDetE.returnOk (ε := SyscallError) <| EptInvocation.poolAssign (ucast asidRepLen offset + base) p sl) σ := by
  rw [eptAssign_prefix, ht, runE_bind_ok (runE_whenE_false (by simp) _ σ),
    runE_bind_ok (runE_whenE_false (by simp [the]) _ σ), runE_bind_ok (runE_liftE (getAsidPool_eq hk)),
    runE_bind_ok (runE_ret _ σ)]
  rfl

theorem eptAssign_full {p base : ObjRef} {sl : CslotPtr} {σ : State Unit}
    (ht : σ.archState.x64AsidTable (asidHighBitsOf base) = some p) {f : AsidLowIndex → Option ObjRef}
    (hk : σ.kheap p = some (.archObj (.asidPool f))) (hfs : freeSet f base = ∅) :
    ExceptT.run (decodeEptAsidPoolAssign (Z := Unit) p base sl) σ = ({(.error .deleteFirst, σ)}, False) := by
  rw [eptAssign_pool ht hk]
  exact runE_bind_err (by rw [runE_whenE_true hfs]; exact runE_throw _ σ)

theorem eptAssign_mem {p base : ObjRef} {sl : CslotPtr} {σ : State Unit}
    (ht : σ.archState.x64AsidTable (asidHighBitsOf base) = some p) {f : AsidLowIndex → Option ObjRef}
    (hk : σ.kheap p = some (.archObj (.asidPool f))) {off : AsidLowIndex} (hoff : off ∈ freeSet f base) :
    (.ok (.poolAssign (ucast asidRepLen off + base) p sl), σ) ∈
      (ExceptT.run (decodeEptAsidPoolAssign (Z := Unit) p base sl) σ).1 ∧
      ¬ (ExceptT.run (decodeEptAsidPoolAssign (Z := Unit) p base sl) σ).2 := by
  have hne : freeSet f base ≠ ∅ := fun h => by rw [h] at hoff; exact hoff
  rw [eptAssign_pool ht hk, runE_bind_ok (runE_whenE_false hne _ σ)]
  refine ⟨runE_liftE_mem (selectExt_mem _ hoff σ) (by rw [runE_ret]; rfl),
    runE_liftE_nofail (selectExt_nofail _ _ σ) fun x σ1 _ => by rw [runE_ret]; exact id⟩

/-- **The spec's perform of an EPT pool assign** (`performEptInvocation (.poolAssign …)`): the slot's level-0
`eptCap` mapped at `asid` (guest address 0), the pool entry `some (r ||| 1)`. -/
theorem performEptAssign_eq {σ : State Unit} {pc : ObjRef} {r : Nat} {cs : CnodeContents} {idx : List Bool}
    (hk : σ.kheap pc = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r) {rt : ObjRef}
    {o : Option (Asid × VSpaceRef)} (hc : cs idx = some (.archObjectCap (.eptCap rt 0 o))) {p : ObjRef}
    {f : AsidLowIndex → Option ObjRef} (hp : σ.kheap p = some (.archObj (.asidPool f))) (asid : Asid) :
    performEptInvocation (Z := Unit) (.poolAssign asid p (pc, idx)) σ =
      ({((), updK (setCnodeSlot σ pc r cs idx (.archObjectCap (.eptCap rt 0 (some (asid, 0))))) p
        (.archObj (.asidPool (Function.update f (asidLowBitsOf asid) (some (rt ||| 1))))))}, False) := by
  have hpc : p ≠ pc := kheap_ne hp hk (fun _ h1 h2 => by subst h1; cases h2)
  unfold performEptInvocation
  dsimp only
  rw [nd_bind_one (getCap_cnode hk hwf hc)]
  show (setCap (Z := Unit) (.archObjectCap (.eptCap rt 0 (some (asid, 0)))) (pc, idx) >>= fun _ =>
    storeAsidPoolEntry p asid (some (rt ||| 1))) σ = _
  rw [nd_bind_one (setCap_cnode _ hk hwf hidx)]
  unfold storeAsidPoolEntry
  have hp' : (setCnodeSlot σ pc r cs idx (.archObjectCap (.eptCap rt 0 (some (asid, 0))))).kheap p =
      some (.archObj (.asidPool f)) := by simp [setCnodeSlot, hpc, hp]
  rw [nd_bind_one (getAsidPool_eq hp'), nd_pure_bind', setAsidPool_eq hp']

/-- The spec after the EPT pool-assign decode: `set_thread_state cur Restart`, then the perform, with the single
outcome `σ'`. -/
def EptAssignSpec (σ : State Unit) (asid ptr : ObjRef) (sl : CslotPtr) (σ' : State Unit) : Prop :=
  (setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
    performEptInvocation (.poolAssign asid ptr sl)) σ = ({((), σ')}, False)

end Spec

/-- **What an EPT pool assign leaves on the spec side** (`AssignF`'s nested analogue): the ASID table's entry `hi`
names the pool `pool`, whose entry `lo` (`asid = hi · 512 + lo`) is written `some (q0 ||| 1)`; every other spec arch
object and the ASID table kept. Gen 42b13: `asid ≠ 0` (FL4's free-entry search skips `base + i = 0`, vspace.rs
l. 1238; `decode_loop1_spec`). -/
def AssignFE (m' : U64 → U64) (x q0 : U64) (σ σ' : Fl4Spec.State Unit) : Prop :=
  ∃ (asid pool hi lo : U64) (f : BitVec 9 → Option Fl4Spec.ObjRef),
    capV m' x = .Ept q0 0#u64 true asid 0#u64 ∧
    hi.val < 2048 ∧ σ.archState.x64AsidTable (Fl4Spec.ucast 11 hi.bv) = some pool.bv ∧
    lo.val < 512 ∧ asid.val = hi.val * 512 + lo.val ∧ asid.val < 2 ^ 20 ∧ asid ≠ 0#u64 ∧
    σ.kheap pool.bv = some (.archObj (.asidPool f)) ∧
    σ'.kheap pool.bv = some (.archObj (.asidPool
      (Function.update f (Fl4Spec.ucast 9 lo.bv) (some (q0.bv ||| 1))))) ∧
    ArchKeepBut pool σ σ' ∧ σ'.archState.x64AsidTable = σ.archState.x64AsidTable

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

omit L in
/-- The nested arm's free-entry search is the native arm's loop. -/
theorem decode_loop2_eq (s : S) (base pool i : U64) :
    vspace.decode_loop2 st s base pool i = vspace.decode_loop1 st s base pool i := rfl

omit L in
theorem or1_bv (x : U64) : (x ||| 1#u64).bv = @HOr.hOr (BitVec 64) (BitVec 64) (BitVec 64) _ x.bv 1 := by simp only [UScalar.bv_or]; rfl

set_option maxHeartbeats 4000000 in
/-- **ASIDPool `Assign` of an unmapped level-0 EPT root** (see the module docstring). -/
theorem assign_rel_ept {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsInvHyps st A th P SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s))
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hS : SR s a σ) {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (ptr base : U64) (hb : base.val % 512 = 0) (hb20 : base.val < 2 ^ 20)
    (length : U64) (slot : obj.Slot) (call : Bool) (buf : U64) (ex : Array obj.Slot 3#usize)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hex : vspace.extra ex 0#usize = ok (some (cslotAddr (pc.bv, idx))))
    {ptr1 asid0 va0 : U64} (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Ept ptr1 0#u64 false asid0 va0))
    (hcan : Canonical ptr1) (hev : ptr1.val % 2 = 0)
    (htcb : ∀ ct : U64, ct.bv = σ.curThread → th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b) :
    vspace.decode st ar s a fl4_abi.label.X86ASIDPoolAssign length slot (.AsidPool ptr base) call buf ex ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ VsErrRel e e' ∧
        ExceptT.run (Fl4Spec.decodeEptAsidPoolAssign (Z := Unit) ptr.bv base.bv (pc.bv, idx)) σ =
          ({(.error e', σ)}, False) ∧
        res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧
        ¬ (ExceptT.run (Fl4Spec.decodeEptAsidPoolAssign (Z := Unit) ptr.bv base.bv (pc.bv, idx)) σ).2 ∧
        ∃ asid σ', (.ok (.poolAssign asid ptr.bv (pc.bv, idx)), σ) ∈
          (ExceptT.run (Fl4Spec.decodeEptAsidPoolAssign (Z := Unit) ptr.bv base.bv (pc.bv, idx)) σ).1 ∧
          EptAssignSpec σ asid ptr.bv (pc.bv, idx) σ' ∧ StateRel th (L.mem res.2.1) σ' ∧
          SlotsValid th (L.mem res.2.1) ∧
          VsRel P (L.mem res.2.1) (L.ksb res.2.1) σ' ∧ SR res.2.1 res.2.2 σ' ∧
          SlotFoot th (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) ∧ KFoot σ σ' ∧
          (∀ b, VsWrite P (L.ksb s) b → L.mem res.2.1 b ≠ L.mem s b → L.mem res.2.1 b = (ptr1 ||| 1#u64)) ∧
          AssignFE (L.mem res.2.1) (cslotAddr (pc.bv, idx)) ptr1 σ σ') ⦄ := by
  have hcs0 := hSt.cnode pc r hpc
  obtain ⟨cs, hkc, hwf, hsl⟩ := hcs0
  generalize hdec : ExceptT.run (Fl4Spec.decodeEptAsidPoolAssign (Z := Unit) ptr.bv base.bv (pc.bv, idx)) σ = dec
  unfold vspace.decode
  refine WP.spec_bind (hH.curT s a σ hS) ?_
  rintro ct hct
  have hlb : (fl4_abi.label.X86ASIDPoolAssign != fl4_abi.label.X86ASIDPoolAssign) = false := by simp
  simp only [hlb, Bool.false_eq_true, ↓reduceIte]
  rw [hex]
  apply ok_bind_spec
  dsimp only
  rw [slot_cap_eq, hcx]
  apply ok_bind_spec
  dsimp only
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold lift
  apply ok_bind_spec
  -- the slot of the EPT cap
  have hxs : IsSlotAt th pc (blVal 0 idx) := Or.inl ⟨r, hpc, hidx ▸ blVal_lt idx⟩
  have hx0 : cslotAddr (pc.bv, idx) = slotOf pc (blVal 0 idx) := slotAddr_ofBl pc idx
  have hxsl : IsSlot th (cslotAddr (pc.bv, idx)) := ⟨pc, _, hxs, hx0⟩
  have hcs : cs idx = some (.archObjectCap (.eptCap ptr1.bv 0 none)) := by
    obtain ⟨c, ac, hc, hac, hca⟩ := hsl idx hidx
    have : c = .Ept ptr1 0#u64 false asid0 va0 := by
      have h2 : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok c := hc
      rw [hcx] at h2; exact (by simpa using h2 : capability.Cap.Ept ptr1 0#u64 false asid0 va0 = c).symm
    subst this
    rw [hac, ← hca.2]; rfl
  have hL : vspace.ASID_LOW_BITS = 9#u64 := by unfold vspace.ASID_LOW_BITS; rfl
  rw [hL]
  step as ⟨i, hi⟩
  refine WP.spec_bind (asid_table_spec s i) ?_
  rintro w rfl
  have hiv : i.val = base.val >>> 9 := by simpa using hi
  have hlt := and_lt i 11 2047#u64 rfl (by decide)
  have htab := hR.table _ hlt
  rw [hi_bv base i hiv] at htab
  by_cases hp : L.mem s (atA (L.ksb s) (i &&& 2047#u64)) = 0#u64
  · simp only [hp, ↓reduceIte]
    refine (WP.spec_ok _).2 ?_
    rw [hp, optRef_zero] at htab
    refine Or.inl ⟨_, .failedLookup false .invalidRoot, rfl,
      Or.inl (show SysErrRel _ (.failedLookup false .invalidRoot) from ⟨rfl, trivial⟩), ?_, rfl, rfl⟩
    rw [← hdec]; exact eptAssign_noPool htab
  · simp only [hp, ↓reduceIte]
    rw [optRef, if_neg hp] at htab
    by_cases hwp : L.mem s (atA (L.ksb s) (i &&& 2047#u64)) = ptr
    · have hne : (L.mem s (atA (L.ksb s) (i &&& 2047#u64)) != ptr) = false := by simp [hwp]
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      rw [hwp] at htab ⊢
      have hpP : ptr ∈ P := hwp ▸ hR.tmem _ hlt hp
      obtain ⟨f, hkf, -⟩ := hR.pool ptr hpP
      have hpf := (hVP.pal ptr hpP).2
      rw [decode_loop2_eq]
      refine WP.spec_bind (decode_loop1_spec s base ptr hpf) ?_
      rintro i1 ⟨hi1le, hall, hfound⟩
      by_cases h512 : i1 = 512#u64
      · simp only [h512, ↓reduceIte]
        refine (WP.spec_ok _).2 ?_
        refine Or.inl ⟨_, .deleteFirst, rfl, Or.inl (show SysErrRel _ .deleteFirst from trivial), ?_, rfl, rfl⟩
        rw [← hdec]
        refine eptAssign_full htab hkf (full_of_none hR hpP hkf base fun j hj => hall j ?_)
        rw [h512]; exact hj
      · simp only [h512, ↓reduceIte]
        have hi1 : i1.val < 512 := by
          have : i1.val ≠ 512 := fun h => h512 (UScalar.eq_of_val_eq h)
          omega
        obtain ⟨h0, he⟩ := hfound hi1
        set asid := core.num.U64.wrapping_add base i1 with hasid
        have hab : asid.val = base.val + i1.val := by
          rw [hasid]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
        have ha20 : asid.val < 2 ^ 20 := by rw [hab]; omega
        have hoff := free_of_found hR hpP hkf base i1 hi1 h0 he
        obtain ⟨hmem, hnf⟩ := eptAssign_mem (sl := (pc.bv, idx)) htab hkf hoff
        rw [ucast64_ucast9 i1 hi1 base] at hmem
        -- `Restart`
        have hkt' : σ.kheap ct.bv = some (.tcb xct) := by rw [hct]; exact hkt
        refine WP.spec_bind (WP.spec_and (hH.restart s a σ ct xct hSt hSV hR hS hct hkt' (htcb ct hct) hact hrun)
          (set_thread_state_slots th hPl s ct sched.TS_RESTART (htcb ct hct) hact)) ?_
        rintro s1 ⟨⟨hSt1, hSV1, hR1, hS1, hk1⟩, hSS1⟩
        set σ1 := stsAct (updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv with hσ1
        have hpct : pc.bv ≠ ct.bv := kheap_ne hkc hkt' (fun _ h1 h2 => by subst h1; cases h2)
        have hptct : ptr.bv ≠ ct.bv := kheap_ne hkf hkt' (fun _ h1 h2 => by subst h1; cases h2)
        have hkc1 : σ1.kheap pc.bv = some (.cnode r cs) := by rw [hσ1, stsAct_kheap]; simp [hpct, hkc]
        have hkf1 : σ1.kheap ptr.bv = some (.archObj (.asidPool f)) := by rw [hσ1, stsAct_kheap]; simp [hptct, hkf]
        -- the cap
        rw [Sched.or1_and_not1 ptr1 hev]
        set nc : Fl4Spec.Cap := .archObjectCap (.eptCap ptr1.bv 0 (some (asid.bv, 0)))
        have hca : CapRel (.Ept ptr1 0#u64 true asid 0#u64) nc := ⟨trivial, rfl⟩
        have hew : EncWf (.Ept ptr1 0#u64 true asid 0#u64) := ⟨hcan, by decide, ha20, by decide⟩
        refine WP.spec_bind (WP.spec_and (set_cap_refines th s1 σ1 hSt1 hSV1 hPl hpc hidx _ _ hca trivial hew)
          (WP.spec_and (set_cap_spec (L := L) _ s1 (.Ept ptr1 0#u64 true asid 0#u64))
            (set_cap_foot hPl hxsl s1 (.Ept ptr1 0#u64 true asid 0#u64) hew))) ?_
        rintro s2 ⟨⟨σ2, hsc, hSt2, hSV2, -, -, -, hfr2⟩, hs2, hF2, hcv2⟩
        have hσ2 : σ2 = setCnodeSlot σ1 pc.bv r cs idx nc := by
          rw [setCap_cnode nc hkc1 hwf hidx] at hsc
          have := congrArg Prod.fst hsc
          simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
          exact this.symm
        subst hσ2
        set σ2 := setCnodeSlot σ1 pc.bv r cs idx nc with hσ2
        have hks2 : L.ksb s2 = L.ksb s := by rw [hs2]; simp [hk1]
        -- the frame of the slot write
        have hfrV : ∀ b, VsWrite P (L.ksb s) b → L.mem s2 b = L.mem s1 b := by
          intro b hb
          obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs (hD b hb)
          exact hfr2 b (hb.aligned hVP) (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
        have hpools : ∀ q ∈ P, σ2.kheap q.bv = σ1.kheap q.bv := by
          intro q hq
          obtain ⟨g, hg, -⟩ := hR1.pool q hq
          have : q.bv ≠ pc.bv := kheap_ne hg hkc1 (fun _ h1 h2 => by subst h1; cases h2)
          simp [hσ2, setCnodeSlot, this]
        have hR2 : VsRel P (L.mem s2) (L.ksb s2) σ2 := by
          rw [hks2]; rw [hk1] at hR1
          exact hR1.frame hfrV rfl hpools
        have hWs : WritesIn st s1 s2 (SlotW th) := by
          refine ⟨by rw [hs2]; simp, by rw [hs2]; simp, fun b hb hn => ?_⟩
          obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs hn
          exact hfr2 b hb (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
        have hS2 := hH.capStable _ _ a _ σ2 hS1 hWs ⟨pc.bv, r, cs, idx, nc, hkc1, rfl⟩
        have hkf2 : σ2.kheap ptr.bv = some (.archObj (.asidPool f)) := (hpools ptr hpP).trans hkf1
        -- the pool write
        have hlo := and_lt asid 9 511#u64 rfl (by decide)
        step as ⟨i3, hi3⟩
        have hval : (asid &&& 511#u64).val = asid.val &&& 511 := by simp [UScalar.val_and]
        have he4 : core.num.U64.wrapping_add ptr i3 = peA ptr (asid &&& 511#u64) := by
          apply UScalar.eq_of_val_eq
          rw [peA_val hpf hlo]
          simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hi3]; omega
        rw [he4, L.write_eq]
        apply ok_bind_spec
        set v := ptr1 ||| 1#u64 with hv
        have hv0 : v ≠ 0#u64 := by rw [hv]; exact Sched.odd_ne_even (by simp)
        set σ3 := updK σ2 ptr.bv (.archObj (.asidPool
          (Function.update f (Fl4Spec.asidLowBitsOf asid.bv) (some (ptr1.bv ||| 1))))) with hσ3
        have hpeW0 : VsWrite P (L.ksb s) (peA ptr (asid &&& 511#u64)) := Or.inr ⟨ptr, hpP, _, hlo, rfl⟩
        have hbo : OutsideObjects th (peA ptr (asid &&& 511#u64)) := hVO _ hpeW0
        have hFt : SlotFoot th (L.mem s) (L.mem (L.wr s2 (peA ptr (asid &&& 511#u64)) v)) (cslotAddr (pc.bv, idx)) :=
          (SlotFoot.of_same hSS1 _).trans (hF2.trans (SlotFoot.wr_out hPl s2 hbo _))
        have hKf : KFoot σ σ3 := (KFoot.sts hkt' _).trans ((KFoot.cnode hkc1 hwf idx nc).trans (KFoot.arch hkf2 _))
        refine (WP.spec_ok _).2 (Or.inr ⟨rfl, by rw [← hdec]; exact hnf, asid.bv, σ3, by rw [← hdec]; exact hmem,
          ?_, ?_, ?_, ?_, ?_, hFt, hKf, ?_, ?_⟩)
        · unfold EptAssignSpec
          rw [← hct, nd_bind_one (Notif.setThreadState_eq .restart hkt')]
          exact performEptAssign_eq hkc1 hwf hidx hcs hkf1 asid.bv
        all_goals
          have hpeW : VsWrite P (L.ksb s) (peA ptr (asid &&& 511#u64)) := Or.inr ⟨ptr, hpP, _, hlo, rfl⟩
          have hpeA : Aligned (peA ptr (asid &&& 511#u64)) := hpeW.aligned hVP
          have hcaps := capAt_wr_nonslot (L := L) hPl s2 hpeA (hD _ hpeW) v
        · exact Vs.StateRel.upd_other (hSt2.of_caps hcaps) hkf2 _
        · exact Vs.SlotsValid.of_caps hSV2 hcaps
        · show VsRel P (L.mem (L.wr s2 (peA ptr (asid &&& 511#u64)) v))
            (L.ksb (L.wr s2 (peA ptr (asid &&& 511#u64)) v)) σ3
          have := hR2.upd_entry (hks2 ▸ hVP) hpP hkf2 hlo v
            (fun b hb hne => L.mem_wr_ne hpeA hb (fun h => hne (UScalar.eq_of_val_eq h).symm)) (L.mem_wr_same hpeA)
          rw [lo_bv, show optRef v = some (ptr1.bv ||| 1) by unfold optRef; rw [if_neg hv0, hv]; exact congrArg some (or1_bv ptr1)] at this
          rw [LawfulStore.ksb_wr]
          exact this
        · refine hH.vsStable s2 _ a σ2 σ3 hS2 ⟨by simp, by simp, fun b hb hn => L.mem_wr_ne hpeA hb fun h => hn ?_⟩
            (Or.inl ⟨ptr.bv, f, _, hkf2, rfl⟩)
          rw [hks2, show b = peA ptr (asid &&& 511#u64) from (UScalar.eq_of_val_eq h).symm]
          exact hpeW
        · intro b hb hne
          by_cases e : peA ptr (asid &&& 511#u64) = b
          · subst e; exact L.mem_wr_same hpeA
          · have hba := hb.aligned hVP
            rw [L.mem_wr_ne hpeA hba (fun h => e (UScalar.eq_of_val_eq h)), hfrV b hb] at hne ⊢
            refine absurd ?_ hne
            have hpools1 : ∀ q ∈ P, σ1.kheap q.bv = σ.kheap q.bv := by
              intro q hq
              obtain ⟨g, hg, -⟩ := hR.pool q hq
              have : q.bv ≠ ct.bv := kheap_ne hg hkt' (fun _ h1 h2 => by subst h1; cases h2)
              rw [hσ1, stsAct_kheap]; simp [this]
            have ht1 : σ1.archState.x64AsidTable = σ.archState.x64AsidTable := by
              rw [hσ1]; unfold stsAct; split <;> rfl
            rw [hk1] at hR1
            exact hR.words_eq hR1 ht1 hpools1 b hb
        · -- `AssignFE`
          have hhi : (i &&& 2047#u64).val = base.val / 512 := by
            have : (i &&& 2047#u64).val = i.val % 2048 := by
              rw [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod i.val 11
            have hb20' : base.val < 1048576 := hb20
            rw [this, hiv, Nat.shiftRight_eq_div_pow]; simp only [Nat.reducePow]; omega
          have hlov : (asid &&& 511#u64).val = i1.val := by
            have : (asid &&& 511#u64).val = asid.val % 512 := by
              rw [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod asid.val 9
            rw [this, hab]; omega
          refine ⟨asid, ptr, i &&& 2047#u64, asid &&& 511#u64, f, ?_, hlt,
            by rw [hi_bv base i hiv]; exact htab, hlo, by rw [hhi, hlov, hab]; omega, ha20, h0, hkf, ?_, ?_, ?_⟩
          · rw [capV_wr_out hPl hxsl s2 hbo, hcv2]
          · rw [hσ3, lo_bv]; exact Function.update_self _ _ _
          · rintro q' ⟨ao, hao⟩ hne
            have h1 : q'.bv ≠ ptr.bv := fun h => hne (eq_of_bv h)
            have h2 : q'.bv ≠ ct.bv := kheap_ne hao hkt' (fun _ h1 h2 => by subst h1; cases h2)
            have h3 : q'.bv ≠ pc.bv := kheap_ne hao hkc (fun _ h1 h2 => by subst h1; cases h2)
            simp [hσ3, updK, hσ2, setCnodeSlot, hσ1, stsAct_kheap, h1, h2, h3]
          · rw [hσ3, hσ2, hσ1]; unfold stsAct; split <;> rfl
    · have hne : (L.mem s (atA (L.ksb s) (i &&& 2047#u64)) != ptr) = true := by simp [hwp]
      simp only [hne, ↓reduceIte]
      rw [show error.invalid_cap Unit 0#u64 = ok (.Err (.Sys (.InvalidCapability 0#u64))) from rfl]
      apply ok_bind_spec
      refine (WP.spec_ok _).2 ?_
      refine Or.inl ⟨_, .invalidCapability 0, rfl, Or.inr ⟨0#u64, rfl, rfl⟩, ?_, rfl, rfl⟩
      rw [← hdec]
      exact eptAssign_wrong htab (fun h => hwp (eq_of_bv h).symm)

end

end

end Fl4Proofs.P3.Vs
