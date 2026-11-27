/-
P3x for virtualization (line virt, gen 15, item 1): **the VCPU retype step, end to end** — gen 14's `init_rel`
(P3/VirtInitWalk) fed into FL4's object creation (`objects::create_arch_object` / `create_object` with
`X86Vcpu`, crates/fl4-core/src/arch/x86_64/objects.rs l. 44-71, objects.rs `create_object`) and into the spec's
retype hook (`fl4InvokeUntypedV`'s `setVcpu v (initVcpu virtKind)`, Ext/VirtFinalise).

* `vzero_of_win`: gen 14's state hypothesis `VZero` from P3's `WinZero` (UntypedFrameBase: the window after the
  retype's clearing, no TCB exception for a VCPU retype) when the object lies in the window.
* **`initListOut_of`**: gen 14's premise `InitListOut` [J] **derived** from mmuAD's VCPU-list invariant `VList`
  (P3/JExtVList) and the placement facts `create_vcpu_growL` (P3/JExtVListSteps) already assumes: `hf` (the VCPUs
  of `V` fit), `hap` (the new object apart from them) and `hhv` (the head word outside the new object). The head
  word is aligned by `VList.hd`, an old head is a VCPU of `V` by `VList.head`, so its `PREV` word is aligned and,
  by `hap`, outside the new object.
* **`create_vcpu_rel`** / **`create_object_vcpu_rel`**: `create_arch_object` / `create_object` with `X86Vcpu`
  return `Cap.Vcpu v` and leave FL4's image at `v` related to `initVcpu virtKind` (`VRelInit`: SVM relation on
  an SVM backend, VMX relation otherwise), with `VZero` from `WinZero` and `InitListOut` from `VList`.
* **`create_vcpu_growLR`**: mmuAD's `create_vcpu_growL` (`Cap.Vcpu v`, `JExtV (insert v V)`, `VList (insert v V)`)
  and the relation together, from one set of premises: `create_vcpu_growL`'s minus its two zero-word
  hypotheses (`hz`, `hzt`, now from `WinZero` as in `create_vcpu_grow_win`), plus `CapAgree` [P] and
  `VirtCodeAgree` [P] (gen 11 / 14, unchanged). **`InitListOut` is no premise here.**
* Spec side: `setVcpu_out`, **`mapMx_setVcpu`** (every address of the list holds the given state afterwards, any
  other object unchanged), **`retypeHook_vcpuAt`** (the hook of `fl4InvokeUntypedV`: every new VCPU is
  `initVcpu virtKind`).
* **`retype_vcpu_rel`**: the two halves joined — FL4's image at a created `v` and the spec's VCPU at `v` after the
  hook: `VRelAt` (`vcpuAt σ' v = some vs` with `vs` related to `memW s'` at `v` on the backend).
* Link-word frame (for retypes of several VCPUs, where the next `init` rewrites the previous object's `PREV`):
  `AgreeAtL` (agreement on the object but its `NEXT` / `PREV` words), **`VcpuRelVmx.congrL`**,
  **`VcpuRelSvm.congrL`**: neither relation reads `NEXT` (0x5008) or `PREV` (0x5010).

Named premises: `CapAgree ar a` [P], `VirtCodeAgree ar a` [P] (unchanged), and those of mmuAD's
`create_vcpu_growL` (all [J] placement facts of the new object, unchanged; copied files below).
**Removed relative to gen 14's `init_rel`: `InitListOut` [J]** (derived), `VZero` (derived).
Files copied byte-identically from branch `par/mmuAD` (b670dadc9; blobs 9e8161f9, e0690dca): `P3/JExtVList.lean`,
`P3/JExtVListSteps.lean` (mmuAD gen 23). New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtInitWalk
import Fl4Proofs.P3.JExtVListSteps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtRetypeInit
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtVcpuRel
open Fl4Proofs.P3.VirtInitWalk

noncomputable section

theorem spec_ex {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ r => P r ⦄) : ∃ v, m = ok v ∧ P v := by
  revert h; cases m <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]

/-- Two posts of one (deterministic) program hold together. -/
theorem spec_and2 {α : Type} {m : Result α} {P Q : α → Prop} (h1 : m ⦃ P ⦄) (h2 : m ⦃ Q ⦄) :
    m ⦃ r => P r ∧ Q r ⦄ := by
  obtain ⟨x, hx, px⟩ := spec_ex h1
  rw [hx] at h2 ⊢
  exact (WP.spec_ok _).2 ⟨px, (WP.spec_ok _).1 h2⟩

/-- The relation `init_rel` gives: on the spec's backend. -/
def VRelInit (mem : Word → Word) (v : Word) : Prop :=
  (virtKind = .svm → VcpuRelSvm mem v (initVcpu virtKind)) ∧
    (virtKind ≠ .svm → VcpuRelVmx mem v (initVcpu virtKind))

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A} {a : A}
variable {V X : Set U64} {th : TypedHeap}

/-- **`VZero` from the retype's window** (`WinZero` without TCB exception; the object inside the window). -/
theorem vzero_of_win {s : S} {v : U64} {A0 k win : Nat} (hwz : WinZero (L.mem s) A0 k win False)
    (hin : A0 ≤ v.val ∧ v.val + 32768 ≤ A0 + win * k) : VZero st s v := fun b hb h1 h2 =>
  (hwz b hb (by omega) (by omega)).resolve_right fun h => h.1

/-- **`InitListOut` [J] derived** (module docstring): from `VList`, the fit of `V`'s VCPUs, the new object apart
from them, and the head word outside the new object. -/
theorem initListOut_of {s : S} (Vl : VList st V th s) (hf : ∀ w ∈ V, w.val % 32768 = 0 ∧ w.val + 32768 ≤ 2 ^ 64)
    {v : U64} (hap : ∀ w ∈ V, w.val + 32768 ≤ v.val ∨ v.val + 32768 ≤ w.val)
    (hhv : (P1.vHeadA st s).val < v.val ∨ v.val + 32768 ≤ (P1.vHeadA st s).val) : InitListOut st s v := by
  refine ⟨Vl.hd.1, hhv, fun hn => ?_⟩
  have hw := Vl.head hn
  have f := hf _ hw
  have e := lay_prev_val f.2
  refine ⟨?_, ?_⟩
  · unfold P1.Aligned; rw [e]; omega
  · unfold OutV; rw [e]; rcases hap _ hw with h | h <;> omega

/-- **`create_arch_object … X86Vcpu v`, related**: `Cap.Vcpu v`, and FL4's image at `v` relates to
`initVcpu virtKind` (premises: module docstring). -/
theorem create_vcpu_rel (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {s : S} {v : U64} (hv : VFits v)
    (hz : VZero st s v) (hl : InitListOut st s v) (dev : Bool) :
    objects.create_arch_object st ar s a fl4_abi.consts.object.X86Vcpu v dev ⦃ r =>
      r.1 = capability.Cap.Vcpu v ∧ VRelInit (memW st r.2.1) v.bv ⦄ := by
  unfold objects.create_arch_object
  rw [if_pos rfl]
  exact WP.spec_bind (init_rel hc hk hv s hz hl) fun s1 h => (WP.spec_ok _).2 ⟨rfl, h⟩

/-- `create_object` with `X86Vcpu` is `create_arch_object` (objects.rs `create_object`'s fall-through). -/
theorem create_object_vcpu (s : S) (v us : U64) (dev : Bool) :
    objects.create_object st ar s a fl4_abi.consts.object.X86Vcpu v us dev =
      objects.create_arch_object st ar s a fl4_abi.consts.object.X86Vcpu v dev := by
  unfold objects.create_object
  simp only [fl4_abi.consts.object.X86Vcpu, fl4_abi.consts.object.Tcb, fl4_abi.consts.object.Endpoint,
    fl4_abi.consts.object.Notification, fl4_abi.consts.object.CapTable, fl4_abi.consts.object.Untyped,
    fl4_abi.consts.object.SchedContext, fl4_abi.consts.object.Reply]
  rfl

/-- **`create_object … X86Vcpu v`, related** (from the retype's window and the VCPU list). -/
theorem create_object_vcpu_rel (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {s : S} (Vl : VList st V th s)
    (hf : ∀ w ∈ V, w.val % 32768 = 0 ∧ w.val + 32768 ≤ 2 ^ 64) {v : U64} (hv : VFits v)
    (hap : ∀ w ∈ V, w.val + 32768 ≤ v.val ∨ v.val + 32768 ≤ w.val)
    (hhv : (P1.vHeadA st s).val < v.val ∨ v.val + 32768 ≤ (P1.vHeadA st s).val)
    {A0 k win : Nat} (hwz : WinZero (L.mem s) A0 k win False) (hin : A0 ≤ v.val ∧ v.val + 32768 ≤ A0 + win * k)
    (us : U64) (dev : Bool) :
    objects.create_object st ar s a fl4_abi.consts.object.X86Vcpu v us dev ⦃ r =>
      r.1 = capability.Cap.Vcpu v ∧ VRelInit (memW st r.2.1) v.bv ⦄ := by
  rw [create_object_vcpu]
  exact create_vcpu_rel hc hk hv (vzero_of_win hwz hin) (initListOut_of Vl hf hap hhv) dev

set_option maxHeartbeats 4000000 in
/-- **mmuAD's `create_vcpu_growL` and the relation together** (module docstring): `hz` / `hzt` from `WinZero`,
`InitListOut` from `VList`. -/
theorem create_vcpu_growLR (hA : P0.ArchTotal ar) (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {s : S}
    (E : JExtV (L := L) V X th s) (P : JWPl V th) (Vl : VList st V th s)
    (hf : ∀ w ∈ V, w.val % 32768 = 0 ∧ w.val + 32768 ≤ 2 ^ 64)
    (hvv : ∀ w ∈ V, ∀ w' ∈ V, w ≠ w' → w.val + 32768 ≤ w'.val ∨ w'.val + 32768 ≤ w.val)
    {v : U64} (hv : VFits v) (hv0 : v ≠ 0#u64) (hvV : v ∉ V)
    (hap : ∀ w ∈ V, w.val + 32768 ≤ v.val ∨ v.val + 32768 ≤ w.val)
    (hhv : ∀ w, w ∈ insert v V → (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val)
    {A0 k win : Nat} (hwz : WinZero (L.mem s) A0 k win False) (hin : A0 ≤ v.val ∧ v.val + 32768 ≤ A0 + win * k)
    (hd : ∀ b, InitW st s v b → ¬ JW V th b)
    {th' : TypedHeap} (htc : ∀ t, th' t = some .tcb ↔ th t = some .tcb) (hsl : ∀ y, IsSlot th' y → IsSlot th y)
    (hko : vTcbA v ≠ P1.vHeadA st s) (dev : Bool) :
    objects.create_arch_object st ar s a fl4_abi.consts.object.X86Vcpu v dev ⦃ r =>
      r.1 = capability.Cap.Vcpu v ∧ JExtV (L := L) (insert v V) X th' r.2.1 ∧
        VList st (insert v V) th' r.2.1 ∧ VRelInit (memW st r.2.1) v.bv ⦄ := by
  have hzv := vzero_of_win hwz hin
  have hv2 := hv.2
  have hv1 := hv.1
  have hz : L.mem s (vPrevA v) = 0#u64 := by
    have e := lay_prev_val hv2
    exact hzv _ (by unfold P1.Aligned; rw [e]; omega) (by rw [e]; omega) (by rw [e]; omega)
  have hzt : L.mem s (vTcbA v) = 0#u64 := by
    have e := lay_vTcb_val hv2
    exact hzv _ (by unfold P1.Aligned; rw [e]; omega) (by rw [e]; omega) (by rw [e]; omega)
  have hl := initListOut_of Vl hf hap (hhv v (Set.mem_insert v V))
  refine WP.spec_mono (spec_and2 (create_vcpu_growL hA E P a Vl hf hvv hv hv0 hvV hap hhv hz hzt hd htc hsl hko dev)
    (create_vcpu_rel hc hk hv hzv hl dev)) ?_
  rintro r ⟨⟨h1, h2, h3⟩, -, h4⟩
  exact ⟨h1, h2, h3, h4⟩

end

/-! ## Spec side: the retype hook -/

section
variable {Z : Type}

theorem setVcpu_out {σ : State Z} {v : ObjRef} {vs : VcpuState} {x : Unit × State Z}
    (hx : x ∈ (setVcpu (Z := Z) v vs σ).1) : x.2 = { σ with kheap := Function.update σ.kheap v (some (.archObj (.vcpu vs))) } := by
  unfold setVcpu setObject at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨k, -, rfl⟩ : ∃ k, σ.kheap v = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap v with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]

/-- **`mapM_x (setVcpu · vs)`**: every address of the list holds `vs`, every other object is unchanged. -/
theorem mapMx_setVcpu (vs : VcpuState) : ∀ (l : List ObjRef) {σ : State Z} {x : Unit × State Z},
    x ∈ (NonDet.mapMx (fun v => setVcpu (Z := Z) v vs) l σ).1 →
      (∀ v ∈ l, vcpuAt x.2 v = some vs) ∧ (∀ p, p ∉ l → x.2.kheap p = σ.kheap p)
  | [], σ, x, hx => by
    unfold NonDet.mapMx NonDet.pure at hx
    rw [Set.mem_singleton_iff.1 hx]
    exact ⟨fun v h => (List.not_mem_nil h).elim, fun _ _ => rfl⟩
  | w :: l, σ, x, hx => by
    obtain ⟨y, hy, hx⟩ := hx
    have e := setVcpu_out hy
    obtain ⟨h1, h2⟩ := mapMx_setVcpu vs l hx
    refine ⟨fun v hv => ?_, fun p hp => ?_⟩
    · by_cases hvl : v ∈ l
      · exact h1 v hvl
      · have hvw : v = w := by
          rcases List.mem_cons.1 hv with h | h
          · exact h
          · exact (hvl h).elim
        subst hvw
        unfold vcpuAt; rw [h2 v hvl, e]; simp
    · have hpw : p ≠ w := fun h => hp (h ▸ List.mem_cons_self)
      have hpl : p ∉ l := fun h => hp (List.mem_cons_of_mem _ h)
      rw [h2 p hpl, e]; simp [Function.update_of_ne hpw]

/-- **The retype hook of `fl4InvokeUntypedV`** (Ext/VirtFinalise): after `mapM_x (setVcpu · (initVcpu
virtKind))` over the new objects, each of them is `initVcpu virtKind`. -/
theorem retypeHook_vcpuAt (l : List ObjRef) {σ : State Z} {x : Unit × State Z}
    (hx : x ∈ (NonDet.mapMx (fun v => setVcpu (Z := Z) v (initVcpu virtKind)) l σ).1) {v : ObjRef} (hv : v ∈ l) :
    vcpuAt x.2 v = some (initVcpu virtKind) :=
  (mapMx_setVcpu _ l hx).1 v hv

/-- The VCPU relation between FL4's memory and the spec's VCPU at `v`, on the spec's backend. -/
def VRelAt (mem : Word → Word) (σ : State Z) (v : Word) : Prop :=
  ∃ vs, vcpuAt σ v = some vs ∧ (virtKind = .svm → VcpuRelSvm mem v vs) ∧ (virtKind ≠ .svm → VcpuRelVmx mem v vs)

/-- **The VCPU retype step, both halves joined**: FL4's image after `create_object … X86Vcpu v` (`VRelInit`) and
the spec's state after the hook for an address list containing `v` relate at `v`. -/
theorem retype_vcpu_rel {mem : Word → Word} {v : Word} (hf : VRelInit mem v) (l : List ObjRef) {σ : State Z}
    {x : Unit × State Z} (hx : x ∈ (NonDet.mapMx (fun v => setVcpu (Z := Z) v (initVcpu virtKind)) l σ).1)
    (hv : v ∈ l) : VRelAt mem x.2 v :=
  ⟨_, retypeHook_vcpuAt l hx hv, hf.1, hf.2⟩

end

/-! ## Link-word frame -/

/-- Agreement on the VCPU object at `v` except its list links `NEXT` (0x5008) and `PREV` (0x5010). -/
def AgreeAtL (mem mem' : Word → Word) (v : Word) : Prop :=
  ∀ o, o < VcpuLay.SIZE → o ≠ 0x5008 → o ≠ 0x5010 → mem' (v + o) = mem (v + o)

theorem vmcsOff_lt_tcb (f : Word) : vmcsOff f < 0x5000 := by
  have h := vmcsIdx_lt f
  have a : VcpuLay.SHADOW.toNat = 4096 := rfl
  rw [BitVec.lt_def]
  unfold vmcsOff
  rw [BitVec.toNat_add, BitVec.toNat_mul, a, toNat_eight]
  simp only [Nat.reducePow] at h ⊢
  show _ < 20480
  omega

theorem ne_links_of_lt {o : Word} (h : o < 0x5000) : o ≠ 0x5008 ∧ o ≠ 0x5010 := by
  constructor <;> (rintro rfl; revert h; decide)

theorem ne_links_of_ge {o : Word} (h : 0x5018 ≤ o) : o ≠ 0x5008 ∧ o ≠ 0x5010 := by
  constructor <;> (rintro rfl; revert h; decide)

theorem gprOff_ge : ∀ i, 0x5018 ≤ gprOff i := by decide
theorem exitOff_ge : ∀ i, 0x5018 ≤ exitOff i := by decide

theorem msrOff_ge {m i : Word} (h : msrSlot m = some i) : 0x5018 ≤ VcpuLay.MSRS + i * 8 := by
  unfold msrSlot at h
  split_ifs at h <;> first | (obtain rfl := Option.some.inj h; decide) | cases h

theorem ioOff_ge (p : BitVec 16) : 0x5018 ≤ vcpuIoOff p := by
  have hp : p.toNat < 65536 := p.isLt
  rw [BitVec.le_def]
  simp [vcpuIoOff, VcpuLay.IO, BitVec.toNat_add, BitVec.toNat_mul]
  omega

theorem svmOff_lt5 {off : Word} (h : Svm.readable off = true) : off < 0x5000 := by
  have h2 : off < Svm.svmEnd := by
    simp only [Svm.readable, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2
  rw [BitVec.lt_def] at h2 ⊢
  exact Nat.lt_of_lt_of_le h2 (by decide)

theorem agL {mem mem' : Word → Word} {v o : Word} (hm : AgreeAtL mem mem' v) (h1 : o < VcpuLay.SIZE)
    (h2 : o ≠ 0x5008 ∧ o ≠ 0x5010) : mem' (v + o) = mem (v + o) := hm o h1 h2.1 h2.2

theorem VcpuRelCommon.congrL {mem mem' : Word → Word} {v : Word} {vs : VcpuState} (hm : AgreeAtL mem mem' v)
    (h : VcpuRelCommon mem v vs) : VcpuRelCommon mem' v vs where
  tcb := by rw [agL hm tcb_lt (by decide)]; exact h.tcb
  valid := by rw [agL hm valid_lt (by decide)]; exact h.valid
  pending := by rw [agL hm pending_lt (by decide)]; exact h.pending
  mrs i := by rw [agL hm (exitOff_lt i) (ne_links_of_ge (exitOff_ge i))]; exact h.mrs i
  gpr i := by rw [agL hm (gprOff_lt i) (ne_links_of_ge (gprOff_ge i))]; exact h.gpr i
  xcr0 := by rw [agL hm xcr0_lt (by decide)]; exact h.xcr0
  ibpb := by rw [agL hm ibpb_lt (by decide)]; exact h.ibpb

/-- **Link-word frame for VMX**: the relation reads neither `NEXT` nor `PREV`. -/
theorem VcpuRelVmx.congrL {mem mem' : Word → Word} {v : Word} {vs : VcpuState} (hm : AgreeAtL mem mem' v)
    (h : VcpuRelVmx mem v vs) : VcpuRelVmx mem' v vs :=
  { VcpuRelCommon.congrL hm h.toVcpuRelCommon with
    vmcs := fun f hf => by
      rw [agL hm (vmcsOff_lt hf) (ne_links_of_lt (vmcsOff_lt_tcb f))]; exact h.vmcs f hf
    msr := fun m i hi => by rw [agL hm (msrOff_lt hi) (ne_links_of_ge (msrOff_ge hi))]; exact h.msr m i hi
    cr2 := by rw [agL hm cr2_lt (by decide)]; exact h.cr2
    io := fun p => by rw [agL hm (ioOff_lt p) (ne_links_of_ge (ioOff_ge p))]; exact h.io p }

/-- **Link-word frame for SVM**. -/
theorem VcpuRelSvm.congrL {mem mem' : Word → Word} {v : Word} {vs : VcpuState} (hm : AgreeAtL mem mem' v)
    (h : VcpuRelSvm mem v vs) : VcpuRelSvm mem' v vs :=
  { VcpuRelCommon.congrL hm h.toVcpuRelCommon with
    vmcb := fun off hr hh hx => by
      rw [agL hm (svmOff_lt hr) (ne_links_of_lt (svmOff_lt5 hr))]; exact h.vmcb off hr hh hx }

theorem VRelInit.congrL {mem mem' : Word → Word} {v : Word} (hm : AgreeAtL mem mem' v) (h : VRelInit mem v) :
    VRelInit mem' v :=
  ⟨fun e => VcpuRelSvm.congrL hm (h.1 e), fun e => VcpuRelVmx.congrL hm (h.2 e)⟩

end
end Fl4Proofs.P3.VirtRetypeInit
