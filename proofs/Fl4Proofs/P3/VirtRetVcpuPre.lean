/-
P3x for virtualization (line virt, gen 22, item 1a): **the pieces of the full VCPU retype** (`retype_full_vcpu`,
P3/VirtRetFullV) that are not the creation loop.

FL4 side:
* `object_size_vcpu`: `objects::object_size(X86Vcpu, _) = Some(bits::VCPU)` = `zOf 14 _` (= 15).
* **`retype_noreset_eq14`**: UntypedRetype's `retype_noreset_eq` (which needs `nt < 14`) for the type number 14
  (`fl4_abi::consts::object::X86Vcpu`): `untyped::retype` without a reset is the untyped cap update, then
  `create_new_objects` (untyped.rs `retype`, the same prefix as for every other type).

Spec side (`fl4InvokeUntypedV`, Ext/VirtFinalise):
* `fl4ObjBitsApi_vcpu` (`= 15`), `retypeAddrs_vcpu` (the hook's addresses are UntypedLoop's `regionPtrs … 32768`);
* `kt_createCap`, `kt_mapMx_createCap`: `create_cap` keeps every object's type (`khT`, UtRetResetJ);
* **`mapMx_setVcpu_det`**: the hook `mapM_x (setVcpu · vs)` over addresses that hold objects of the VCPU type is
  deterministic: one outcome, the heap updated there;
* **`fl4InvokeUntypedV_vcpu_run`**: the V invocation for `.archObject .vcpuObj` is the ported invocation's single
  outcome followed by the hook's single outcome.

No premise (no [J]/[P]/[W]). New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtLoopSharp
import Fl4Proofs.P3.UntypedSuccess
import Fl4Proofs.P3.UtRetResetJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtRetVcpuPre
open fl4_core Fl4Proofs.P3

noncomputable section

/-! ## FL4: the retype prefix for type 14 -/

theorem object_size_vcpu (nt us : U64) (hn : nt.val = 14) :
    objects.object_size nt us = ok (some ⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩) := by
  have h : nt = fl4_abi.consts.object.X86Vcpu := by unfold fl4_abi.consts.object.X86Vcpu; scalar_tac
  have hz : zOf nt.val us.val = 15 := by rw [hn]; simp [zOf]
  unfold objects.object_size
  rw [if_pos h, hz]
  have e : fl4_abi.consts.bits.VCPU = (⟨BitVec.ofNat 64 15⟩ : U64) :=
    UScalar.eq_of_val_eq (by
      unfold fl4_abi.consts.bits.VCPU
      first | rfl | decide | (simp; done) | scalar_tac | (simp; rfl))
  rw [e]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`retype_noreset_eq` for `X86Vcpu`** (module docstring). -/
theorem retype_noreset_eq14 {A : Type} (arI : machine.Arch A) (s : S) (ar : A) (slot base nt us dest off win : U64)
    (dev : Bool) (hn : nt.val = 14) (hz : zOf nt.val us.val < 64)
    (p sb fi : U64) (dev' : Bool) (hcap : capAt (L.mem s) slot = ok (.Untyped p sb fi dev')) :
    ∃ total : U64, total.bv = win.bv <<< zOf nt.val us.val ∧
      untyped.retype st arI s ar slot false base nt us dest off win dev = (do
        let s1 ← obj.Slot.set_cap st slot s
          (.Untyped p sb (core.num.U64.wrapping_sub (core.num.U64.wrapping_add base total) p) dev')
        let (s2, a2) ← objects.create_new_objects st arI s1 ar nt slot dest off win base us dev
        ok (.Ok (), s2, a2)) := by
  have h63 : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val = zOf nt.val us.val := by
    have : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val =
        (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64).val % 64 := by
      simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
    rw [this]
    show (BitVec.ofNat 64 (zOf nt.val us.val)).toNat % 64 = _
    simp; omega
  obtain ⟨total, htot, htb⟩ : ∃ total, (win <<< ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64)) =
      ok total ∧ total.bv = win.bv <<< zOf nt.val us.val := by
    have := spec_exists (UScalar.ShiftLeft_spec win ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64) _
      (by rw [h63]; simp [UScalarTy.U64_numBits_eq]; omega) rfl)
    obtain ⟨v, hv, -, hb⟩ := this
    exact ⟨v, hv, by rw [hb, h63]⟩
  refine ⟨total, htb, ?_⟩
  unfold untyped.retype
  simp only [Bool.false_eq_true, ↓reduceIte, object_size_vcpu nt us hn, lift, bind_ok,
    core.option.Option.unwrap_or, htot, slot_cap_eq, hcap]

end

/-! ## Spec: the VCPU retype hook -/

section
open Fl4Spec

theorem fl4ObjBitsApi_vcpu (us : Nat) : fl4ObjBitsApi (.archObject .vcpuObj) us = 15 := rfl

theorem retypeAddrs_vcpu (ptr : ObjRef) (n us : Nat) :
    retypeAddrs fl4ObjBitsApi ptr n us (.archObject .vcpuObj) = regionPtrs ptr n 32768 := rfl

theorem kt_createCap (t : ApiObjectType) (b : Nat) (u : CslotPtr) (d : Bool) (x : CslotPtr × ObjRef) :
    Vs.FK khT (createCap (Z := Unit) t b u d x) := by
  obtain ⟨dest, oref⟩ := x
  unfold createCap setCdt setOriginal
  exact Vs.dk_bind (Vs.dk_gets _) fun _ => Vs.dk_bind (Vs.dk_gets _) fun _ =>
    Vs.dk_bind (Vs.dk_get_put fun _ => rfl) fun _ =>
    Vs.dk_bind (kt_deo _) fun _ =>
    Vs.dk_bind (Vs.dk_bind (Vs.dk_gets _) fun _ => Vs.dk_modify fun _ => rfl) fun _ => kt_setCap _ _

theorem kt_mapMx_createCap (t : ApiObjectType) (b : Nat) (u : CslotPtr) (d : Bool)
    (l : List (CslotPtr × ObjRef)) : Vs.FK khT (NonDet.mapMx (createCap (Z := Unit) t b u d) l) :=
  Vs.dk_mapMx (fun x => kt_createCap t b u d x) l

/-- **The hook is deterministic** on addresses holding objects of the VCPU type (module docstring). -/
theorem mapMx_setVcpu_det (vs : VcpuState) : ∀ (l : List ObjRef) (σ : State Unit),
    (∀ v ∈ l, ∃ k, σ.kheap v = some k ∧ aType k = aType (.archObj (.vcpu vs))) →
    NonDet.mapMx (fun v => setVcpu (Z := Unit) v vs) l σ =
      ({((), { σ with kheap := fun p => if p ∈ l then some (.archObj (.vcpu vs)) else σ.kheap p })}, False)
  | [], σ, _ => by
    rw [mapMx_nil]
    congr
  | w :: l, σ, h => by
    obtain ⟨k, hk, ht⟩ := h w List.mem_cons_self
    have e1 : setVcpu (Z := Unit) w vs σ = ({((), Notif.updK σ w (.archObj (.vcpu vs)))}, False) :=
      Notif.setObject_eq hk ht
    rw [mapMx_cons_one (f := fun v => setVcpu (Z := Unit) v vs) e1]
    have h' : ∀ v ∈ l, ∃ k, (Notif.updK σ w (.archObj (.vcpu vs))).kheap v = some k ∧
        aType k = aType (.archObj (.vcpu vs)) := by
      intro v hv
      by_cases e : v = w
      · subst e; exact ⟨_, by simp, rfl⟩
      · obtain ⟨k', hk', ht'⟩ := h v (List.mem_cons_of_mem _ hv)
        exact ⟨k', by simp [Function.update_of_ne e, hk'], ht'⟩
    rw [mapMx_setVcpu_det vs l _ h']
    have ek : (fun p => if p ∈ l then some (KernelObject.archObj (.vcpu vs))
        else (Notif.updK σ w (.archObj (.vcpu vs))).kheap p) =
        (fun p => if p ∈ w :: l then some (KernelObject.archObj (.vcpu vs)) else σ.kheap p) := by
      funext p
      by_cases hp : p ∈ l
      · simp [hp]
      · by_cases e : p = w
        · subst e; simp [hp]
        · simp [hp, e, Function.update_of_ne e]
    rw [ek]
    rfl

/-- **The V invocation of a VCPU retype** (module docstring). -/
theorem fl4InvokeUntypedV_vcpu_run (src : CslotPtr) (base rb : ObjRef) (sz : Nat) (slots : List CslotPtr) (dev : Bool)
    {σ σf σh : State Unit}
    (h1 : (fl4InvokeUntyped (Z := Unit) (.retype src false base rb (.archObject .vcpuObj) sz slots dev)).run σ =
      ({(.ok (), σf)}, False))
    (h2 : NonDet.mapMx (fun v => setVcpu (Z := Unit) v (initVcpu virtKind))
      (retypeAddrs fl4ObjBitsApi rb slots.length sz (.archObject .vcpuObj)) σf = ({((), σh)}, False)) :
    (fl4InvokeUntypedV (Z := Unit) (.retype src false base rb (.archObject .vcpuObj) sz slots dev)).run σ =
      ({(.ok (), σh)}, False) := by
  unfold fl4InvokeUntypedV
  rw [ExceptT.run_bind]
  rw [nd_bind_one h1]
  show (NonDetE.liftE (NonDet.when _ _)).run σf = _
  simp only [NonDet.when, if_pos rfl]
  exact run_liftE' h2

end

end
end Fl4Proofs.P3.VirtRetVcpuPre
