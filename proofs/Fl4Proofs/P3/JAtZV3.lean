/-
P3 (line mmuAD, gen 30): **`JAtZV3` — the VM-epoch invariant with the VCPU field relation** (gen 29's "Next"
item 1 and the first half of item 2).

`JAtZV3 V X … s a σ` := `JAtZV2 V X … s a σ` ∧ **`VOnly V σ`** (gen 29's [J], now a field) ∧
**`VRel V σ (L.mem s)`**: every `v ∈ V`'s spec VCPU object is related to FL4's 32 KiB image at `v` by the virt
line's field relation `Fl4Spec.VcpuRel virtKind` (Ext/VirtRelBase, VirtRelVmx, VirtRelSvm; brought from par/virt
2d9a5b4bf), over the word view `vmemW (L.mem s)` of FL4's memory (`vmemW m w` = `m w` at 8-aligned `w`, 0 elsewhere:
the relation reads only 8-aligned words of a 32 KiB-aligned object, and FL4's store model (`P1.WritesIn`) speaks
only of aligned words).

On a platform without x86 virtualization (`virtKind = none`) `VcpuRel` is `False`, so `VRel` forces `V` to have no
spec VCPU there; P2's boot has `V = ∅`.

## Offsets (`VUnread`)

`VUnread o` says the relation reads no word at offset `o` other than `TCB` (`tcb` field). `VUnread.ofRange`: every
offset in `[TCB, REGS)` other than `XCR0`, `CR2`, `PENDING`, `VALID`, `VM_IBPB_DEFER` (so `TCB`, `NEXT`, `PREV`,
`SVM_CPU`, …): VMCS shadow places are below `TCB` (`v3_vmcs_lt`: FL4's 11-bit index), VMCB words below `svmEnd`,
GPRs/MSRs/exit MRs at or above `REGS`, the I/O bitmap at or above `IO`. `v3_rel`: a memory change at one unread
offset keeps the relation with the `tcb` field read from the new `TCB` word; `v3_rel'`: unchanged if that offset
is not `TCB`.

## Preservation

* Boot **`JBoot.jAtZV3_w1`** (no premise: `σ1` has no VCPU object, `vonly_σ1`); **`JAtZV3.of_native`** (V = ∅;
  `VOnly ∅ σ'` is an argument — "no spec VCPU object", as `RunVmB` / `VList` are for `JAtZV2.of_native`).
* Frames: **`JAtZV3.ofB`**, **`ofBS`** (one more argument than `JAtZV2.ofBS`: `hnv`, every VCPU object after was
  there before, unchanged), **`ofTK`** (from `ScTKw`: `zv_tk_v`), **`archV`**. The FL4 writes lie in `OObj`, which
  is outside every VCPU (`JAtZV.oobj_v`), so the images are unchanged (`v3_agreeW`, `VirtVcpuRel.VcpuRel.congr`).
* Scheduler steps lifted: **`JAtZV3.switchJ`**, **`cancelYieldJ`**, **`runPostJ`** (same premises as at `JAtZV2`).
* VCPU words: **`JAtZV3.vcpuWr`** — a write of an *unread* word (offset in `[TCB, REGS)` minus the six related
  words and the link words, e.g. `SVM_CPU`) keeps `JAtZV3` with the spec unchanged; **`JAtZV3.vcpuStep`** — any
  other non-link VCPU word write **needs a paired spec update**: the spec's new VCPU `vs'` (same `tcb`) related to
  the new image (`hR`, stated, the caller's obligation); **`JAtZV3.vcpuSpec`** the spec-only update, same shape.
* Binding: **`JAtZV3.bind`** / **`unbind`** (spec VCPU exactly `{ vs with tcb := some t }` / `{ vs with tcb := none }`,
  as `associateVcpuTcb` / `vcpuDetach` write it; the `TCB` word and the `tcb` field change together, `vrelLink`).

Which FL4 steps need a paired spec update: every write of a related VCPU word (VMCS shadow / VMCB words, GPRs, MSR
area, `XCR0`, `CR2`, `PENDING`, `VALID`, `VM_IBPB_DEFER`, exit MRs, I/O bitmap) — FL4's `vcpu::decode` Write*
invocations, `vcpu::enter` (staging, `VALID := 0`, `PENDING := 0`), `vcpu::report` (`PENDING := 0`), `vcpu::init`.
None of these is lifted to `JAtZV2`/`JAtZV3` yet; the binding writes and `SVM_CPU` (detach) are handled here.

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZBDetach
import Fl4Proofs.P3.JAtZBYield
import Fl4Proofs.P3.JAtZBRunPostV
import Fl4Proofs.P3.VirtVcpuRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## The word view and the relation -/

/-- FL4's memory as a function on words: the 64-bit word at an 8-aligned address, 0 at the others (module
docstring). -/
def vmemW (m : U64 → U64) : Fl4Spec.Word → Fl4Spec.Word := fun w => if w.toNat % 8 = 0 then (m ⟨w⟩).bv else 0

/-- **The VCPU field relation at every VCPU of `V`** (module docstring). -/
def VRel (V : Set U64) (σ : Fl4Spec.State Unit) (m : U64 → U64) : Prop :=
  ∀ v ∈ V, ∀ vs : Fl4Spec.VcpuState, σ.kheap v.bv = some (.archObj (.vcpu vs)) →
    Fl4Spec.VcpuRel Fl4Spec.virtKind (vmemW m) v.bv vs

/-! ## Offsets the relation does not read -/

/-- The relation reads no word at offset `o0`, except possibly through the `tcb` field. -/
structure VUnread (o0 : Fl4Spec.Word) : Prop where
  valid : o0 ≠ Fl4Spec.VcpuLay.VALID
  pending : o0 ≠ Fl4Spec.VcpuLay.PENDING
  mrs : ∀ i, o0 ≠ Fl4Spec.exitOff i
  gpr : ∀ i, o0 ≠ Fl4Spec.gprOff i
  xcr0 : o0 ≠ Fl4Spec.VcpuLay.XCR0
  ibpb : o0 ≠ Fl4Spec.VcpuLay.VM_IBPB_DEFER
  vmcs : ∀ f, o0 ≠ Fl4Spec.vmcsOff f
  msr : ∀ m i, Fl4Spec.msrSlot m = some i → o0 ≠ Fl4Spec.VcpuLay.MSRS + i * 8
  cr2 : o0 ≠ Fl4Spec.VcpuLay.CR2
  io : ∀ p, o0 ≠ Fl4Spec.vcpuIoOff p
  vmcb : ∀ off, Fl4Spec.Svm.readable off = true → o0 ≠ off

theorem v3_exit_ge : ∀ i : Fin 30, 20992 ≤ (Fl4Spec.exitOff i).toNat := by decide

theorem v3_gpr_ge : ∀ i : Fin 15, 20736 ≤ (Fl4Spec.gprOff i).toNat := by decide

theorem v3_vmcs_lt (f : Fl4Spec.Word) : (Fl4Spec.vmcsOff f).toNat < 20480 := by
  have h := VirtVcpuRel.vmcsIdx_lt f
  have a : Fl4Spec.VcpuLay.SHADOW.toNat = 4096 := rfl
  unfold Fl4Spec.vmcsOff
  rw [BitVec.toNat_add, BitVec.toNat_mul, a, VirtVcpuRel.toNat_eight]
  simp only [Nat.reducePow] at h ⊢
  omega

theorem v3_msr_ge {m i : Fl4Spec.Word} (h : Fl4Spec.msrSlot m = some i) :
    20864 ≤ (Fl4Spec.VcpuLay.MSRS + i * 8).toNat := by
  unfold Fl4Spec.msrSlot at h
  split at h
  · obtain rfl := Option.some.inj h; decide
  split at h
  · obtain rfl := Option.some.inj h; decide
  split at h
  · obtain rfl := Option.some.inj h; decide
  split at h
  · obtain rfl := Option.some.inj h; decide
  split at h
  · obtain rfl := Option.some.inj h; decide
  · cases h

theorem v3_io_ge (p : BitVec 16) : 24576 ≤ (Fl4Spec.vcpuIoOff p).toNat := by
  have hp : p.toNat < 65536 := p.isLt
  simp [Fl4Spec.vcpuIoOff, Fl4Spec.VcpuLay.IO, BitVec.toNat_add, BitVec.toNat_mul]
  omega

theorem v3_svmEnd : Fl4Spec.Svm.svmEnd.toNat < 20480 := by decide

theorem v3_vmcb_lt {off : Fl4Spec.Word} (h : Fl4Spec.Svm.readable off = true) : off.toNat < 20480 := by
  have h2 : off < Fl4Spec.Svm.svmEnd := by
    simp only [Fl4Spec.Svm.readable, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2
  rw [BitVec.lt_def] at h2
  have := v3_svmEnd
  omega

/-- **Every offset of `[TCB, REGS)` but the five related fixed words is unread** (module docstring). -/
theorem VUnread.ofRange {o0 : Fl4Spec.Word} (h1 : 20480 ≤ o0.toNat) (h2 : o0.toNat < 20736)
    (n1 : o0.toNat ≠ 20504) (n2 : o0.toNat ≠ 20512) (n3 : o0.toNat ≠ 20520) (n4 : o0.toNat ≠ 20528)
    (n5 : o0.toNat ≠ 20544) : VUnread o0 where
  valid := fun e => n4 (by rw [e]; rfl)
  pending := fun e => n3 (by rw [e]; rfl)
  mrs := fun i e => by have := v3_exit_ge i; rw [← e] at this; omega
  gpr := fun i e => by have := v3_gpr_ge i; rw [← e] at this; omega
  xcr0 := fun e => n1 (by rw [e]; rfl)
  ibpb := fun e => n5 (by rw [e]; rfl)
  vmcs := fun f e => by have := v3_vmcs_lt f; rw [← e] at this; omega
  msr := fun m i hi e => by have := v3_msr_ge hi; rw [← e] at this; omega
  cr2 := fun e => n2 (by rw [e]; rfl)
  io := fun p e => by have := v3_io_ge p; rw [← e] at this; omega
  vmcb := fun off hr e => by have := v3_vmcb_lt hr; rw [← e] at this; omega

theorem VUnread.tcb : VUnread Fl4Spec.VcpuLay.TCB :=
  VUnread.ofRange (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

section
open Fl4Spec

theorem v3_common {mem mem' : Word → Word} {v o0 : Word} {vs : VcpuState} (hu : VUnread o0)
    (hm : ∀ o, o < VcpuLay.SIZE → o ≠ o0 → mem' (v + o) = mem (v + o)) (h : VcpuRelCommon mem v vs) :
    VcpuRelCommon mem' v { vs with tcb := vcpuTcbRef (mem' (v + VcpuLay.TCB)) } where
  tcb := rfl
  valid := by rw [hm _ VirtVcpuRel.valid_lt (Ne.symm hu.valid)]; exact h.valid
  pending := by rw [hm _ VirtVcpuRel.pending_lt (Ne.symm hu.pending)]; exact h.pending
  mrs i := by rw [hm _ (VirtVcpuRel.exitOff_lt i) (Ne.symm (hu.mrs i))]; exact h.mrs i
  gpr i := by rw [hm _ (VirtVcpuRel.gprOff_lt i) (Ne.symm (hu.gpr i))]; exact h.gpr i
  xcr0 := by rw [hm _ VirtVcpuRel.xcr0_lt (Ne.symm hu.xcr0)]; exact h.xcr0
  ibpb := by rw [hm _ VirtVcpuRel.ibpb_lt (Ne.symm hu.ibpb)]; exact h.ibpb

theorem v3_vmx {mem mem' : Word → Word} {v o0 : Word} {vs : VcpuState} (hu : VUnread o0)
    (hm : ∀ o, o < VcpuLay.SIZE → o ≠ o0 → mem' (v + o) = mem (v + o)) (h : VcpuRelVmx mem v vs) :
    VcpuRelVmx mem' v { vs with tcb := vcpuTcbRef (mem' (v + VcpuLay.TCB)) } :=
  { v3_common hu hm h.toVcpuRelCommon with
    vmcs := fun f hf => by rw [hm _ (VirtVcpuRel.vmcsOff_lt hf) (Ne.symm (hu.vmcs f))]; exact h.vmcs f hf
    msr := fun m i hi => by rw [hm _ (VirtVcpuRel.msrOff_lt hi) (Ne.symm (hu.msr m i hi))]; exact h.msr m i hi
    cr2 := by rw [hm _ VirtVcpuRel.cr2_lt (Ne.symm hu.cr2)]; exact h.cr2
    io := fun p => by rw [hm _ (VirtVcpuRel.ioOff_lt p) (Ne.symm (hu.io p))]; exact h.io p }

theorem v3_svm {mem mem' : Word → Word} {v o0 : Word} {vs : VcpuState} (hu : VUnread o0)
    (hm : ∀ o, o < VcpuLay.SIZE → o ≠ o0 → mem' (v + o) = mem (v + o)) (h : VcpuRelSvm mem v vs) :
    VcpuRelSvm mem' v { vs with tcb := vcpuTcbRef (mem' (v + VcpuLay.TCB)) } :=
  { v3_common hu hm h.toVcpuRelCommon with
    vmcb := fun off hr hh hx => by
      rw [hm _ (VirtVcpuRel.svmOff_lt hr) (Ne.symm (hu.vmcb off hr))]; exact h.vmcb off hr hh hx }

/-- **One unread word changed**: the relation holds with the `tcb` field read from the new `TCB` word. -/
theorem v3_rel {k : VirtKind} {mem mem' : Word → Word} {v o0 : Word} {vs : VcpuState} (hu : VUnread o0)
    (hm : ∀ o, o < VcpuLay.SIZE → o ≠ o0 → mem' (v + o) = mem (v + o)) (h : VcpuRel k mem v vs) :
    VcpuRel k mem' v { vs with tcb := vcpuTcbRef (mem' (v + VcpuLay.TCB)) } := by
  cases k with
  | vmx => exact v3_vmx hu hm h
  | svm => exact v3_svm hu hm h
  | none => exact h.elim
  | armEl2 => exact h.elim

theorem v3_tcb {k : VirtKind} {mem : Word → Word} {v : Word} {vs : VcpuState} (h : VcpuRel k mem v vs) :
    vs.tcb = vcpuTcbRef (mem (v + VcpuLay.TCB)) := by
  cases k with
  | vmx => exact (h : VcpuRelVmx mem v vs).tcb
  | svm => exact (h : VcpuRelSvm mem v vs).tcb
  | none => exact h.elim
  | armEl2 => exact h.elim

/-- **One unread word other than `TCB` changed**: the relation is kept. -/
theorem v3_rel' {k : VirtKind} {mem mem' : Word → Word} {v o0 : Word} {vs : VcpuState} (hu : VUnread o0)
    (hm : ∀ o, o < VcpuLay.SIZE → o ≠ o0 → mem' (v + o) = mem (v + o)) (hne : VcpuLay.TCB ≠ o0)
    (h : VcpuRel k mem v vs) : VcpuRel k mem' v vs := by
  have h1 := v3_rel hu hm h
  have e : vcpuTcbRef (mem' (v + VcpuLay.TCB)) = vs.tcb := by
    rw [hm _ VirtVcpuRel.tcb_lt hne]; exact (v3_tcb h).symm
  rw [e] at h1
  exact h1

end

/-! ## FL4 memory and the word view -/

theorem v3_toNat_add {u : U64} {o : Fl4Spec.Word} (hf : u.val + 32768 ≤ 2 ^ 64) (ho : o < Fl4Spec.VcpuLay.SIZE) :
    (u.bv + o).toNat = u.val + o.toNat := by
  have hs : (Fl4Spec.VcpuLay.SIZE).toNat = 32768 := rfl
  have h1 : o.toNat < 32768 := by rw [BitVec.lt_def, hs] at ho; exact ho
  have hv : u.val = u.bv.toNat := rfl
  rw [BitVec.toNat_add, ← hv]
  exact Nat.mod_eq_of_lt (by omega)

/-- FL4 memories that agree on the aligned words of `u`'s object except at offset `o0` give word views that agree
there. -/
theorem v3_agree {m m' : U64 → U64} {u : U64} (hf : u.val + 32768 ≤ 2 ^ 64) {o0 : Fl4Spec.Word}
    (h : ∀ b : U64, P1.Aligned b → u.val ≤ b.val → b.val < u.val + 32768 → b.val ≠ u.val + o0.toNat →
      m' b = m b) :
    ∀ o, o < Fl4Spec.VcpuLay.SIZE → o ≠ o0 → vmemW m' (u.bv + o) = vmemW m (u.bv + o) := by
  intro o ho hne
  have e := v3_toNat_add hf ho
  have hs : (Fl4Spec.VcpuLay.SIZE).toNat = 32768 := rfl
  have h1 : o.toNat < 32768 := by rw [BitVec.lt_def, hs] at ho; exact ho
  unfold vmemW
  by_cases ha : (u.bv + o).toNat % 8 = 0
  · rw [if_pos ha, if_pos ha]
    have hb : m' ⟨u.bv + o⟩ = m ⟨u.bv + o⟩ := by
      refine h _ ha (by show u.val ≤ (u.bv + o).toNat; omega) (by show (u.bv + o).toNat < u.val + 32768; omega) ?_
      show (u.bv + o).toNat ≠ u.val + o0.toNat
      rw [e]
      intro e2
      exact hne (BitVec.eq_of_toNat_eq (by omega))
    rw [hb]
  · rw [if_neg ha, if_neg ha]

theorem v3_agreeAll {m m' : U64 → U64} {u : U64} (hf : u.val + 32768 ≤ 2 ^ 64)
    (h : ∀ b : U64, P1.Aligned b → u.val ≤ b.val → b.val < u.val + 32768 → m' b = m b) :
    VirtVcpuRel.AgreeAt (vmemW m) (vmemW m') u.bv := fun o ho =>
  v3_agree hf (o0 := Fl4Spec.VcpuLay.SIZE) (fun b hb g1 g2 _ => h b hb g1 g2) o ho
    (fun e => by rw [BitVec.lt_def, e] at ho; exact Nat.lt_irrefl _ ho)

/-- The word view of `v`'s `TCB` word is FL4's `vTcbA v`. -/
theorem v3_vmemW_tcb {v : U64} (hf : v.val % 32768 = 0 ∧ v.val + 32768 ≤ 2 ^ 64) (m : U64 → U64) :
    vmemW m (v.bv + Fl4Spec.VcpuLay.TCB) = (m (vTcbA v)).bv := by
  have e := v3_toNat_add hf.2 VirtVcpuRel.tcb_lt
  have ht : Fl4Spec.VcpuLay.TCB.toNat = 20480 := rfl
  rw [ht] at e
  have hvt := lay_vTcb_val hf.2
  have ha : (v.bv + Fl4Spec.VcpuLay.TCB).toNat % 8 = 0 := by rw [e]; omega
  unfold vmemW
  rw [if_pos ha]
  rw [show (⟨v.bv + Fl4Spec.VcpuLay.TCB⟩ : U64) = vTcbA v from
    UScalar.eq_of_val_eq (by show (v.bv + Fl4Spec.VcpuLay.TCB).toNat = (vTcbA v).val; rw [e, hvt])]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- Writes outside every VCPU of `V` keep every image. -/
theorem v3_agreeW {V : Set U64} {s s' : S} {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hfit : ∀ u ∈ V, u.val + 32768 ≤ 2 ^ 64)
    (hn : ∀ u ∈ V, ∀ b, W b → b.val < u.val ∨ u.val + 32768 ≤ b.val) :
    ∀ u ∈ V, VirtVcpuRel.AgreeAt (vmemW (L.mem s)) (vmemW (L.mem s')) u.bv := fun u hu =>
  v3_agreeAll (hfit u hu) fun b hb g1 g2 => hw.mem_eq hb fun hW => by
    rcases hn u hu b hW with h | h <;> omega

end

/-! ## `VRel` / `VOnly` frames -/

theorem VRel.frame {V : Set U64} {σ σ' : Fl4Spec.State Unit} {m m' : U64 → U64} (h : VRel V σ m)
    (hk : ∀ u ∈ V, ∀ vs : Fl4Spec.VcpuState, σ'.kheap u.bv = some (.archObj (.vcpu vs)) →
      σ.kheap u.bv = some (.archObj (.vcpu vs)))
    (hm : ∀ u ∈ V, VirtVcpuRel.AgreeAt (vmemW m) (vmemW m') u.bv) : VRel V σ' m' :=
  fun u hu vs hv => VirtVcpuRel.VcpuRel.congr (hm u hu) (h u hu vs (hk u hu vs hv))

theorem v3_bv_ne {u p : U64} (e : u ≠ p) : u.bv ≠ p.bv := fun h =>
  e (UScalar.eq_of_val_eq (show u.bv.toNat = p.bv.toNat by rw [h]))

/-- `VRel` after the spec replaces the VCPU object at `p ∈ V`. -/
theorem VRel.upd {V : Set U64} {σ : Fl4Spec.State Unit} {m m' : U64 → U64} (h : VRel V σ m) {p : U64}
    (vs' : Fl4Spec.VcpuState) (hR : Fl4Spec.VcpuRel Fl4Spec.virtKind (vmemW m') p.bv vs')
    (hm : ∀ u ∈ V, u ≠ p → VirtVcpuRel.AgreeAt (vmemW m) (vmemW m') u.bv) :
    VRel V (Notif.updK σ p.bv (.archObj (.vcpu vs'))) m' := by
  intro u hu vs hk
  by_cases e : u = p
  · rw [e] at hk ⊢
    simp [Notif.updK] at hk
    subst hk
    exact hR
  · have hk' : σ.kheap u.bv = some (.archObj (.vcpu vs)) := by simpa [Notif.updK, v3_bv_ne e] using hk
    exact VirtVcpuRel.VcpuRel.congr (hm u hu e) (h u hu vs hk')

theorem VOnly.updV {V : Set U64} {σ : Fl4Spec.State Unit} (h : VOnly V σ) {p : U64} (hp : p ∈ V)
    (o : Fl4Spec.KernelObject) : VOnly V (Notif.updK σ p.bv o) := by
  intro q vs hq
  by_cases e : q = p.bv
  · exact ⟨p, hp, e⟩
  · exact h q vs (by simpa [Notif.updK, e] using hq)

theorem VOnly.frame {V : Set U64} {σ σ' : Fl4Spec.State Unit} (h : VOnly V σ)
    (hk : ∀ p (vs : Fl4Spec.VcpuState), σ'.kheap p = some (.archObj (.vcpu vs)) →
      σ.kheap p = some (.archObj (.vcpu vs))) : VOnly V σ' :=
  fun p vs hp => h p vs (hk p vs hp)

/-- An SC-code spec step (`ScTKw` with no thread-state change) creates no VCPU object and changes none. -/
theorem zv_tk_v {σ σ' : Fl4Spec.State Unit} (h : Sched.ScTKw (fun _ => False) σ σ') :
    ∀ p (vs : Fl4Spec.VcpuState), σ'.kheap p = some (.archObj (.vcpu vs)) →
      σ.kheap p = some (.archObj (.vcpu vs)) := by
  intro o vs ho
  have k := h.kh o
  rw [ho] at k
  cases e : σ.kheap o with
  | none => rw [e] at k; exact k.elim
  | some ko =>
    rw [e] at k
    change Sched.TKObj False ko (.archObj (.vcpu vs)) at k
    rcases k with k | ⟨_, _, -, h2, -, -⟩ | ⟨_, _, _, -, h2⟩ | ⟨_, _, -, h2, -⟩ | ⟨_, _, -, h2, -⟩
    · rw [k]
    all_goals cases h2

/-! ## `JAtZV3` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The VM-epoch invariant with the VCPU field relation** (module docstring). -/
structure JAtZV3 (V X : Set U64) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
    (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  z2 : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ
  vo : VOnly V σ
  vr : VRel V σ (L.mem s)

end

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P1
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- OObj writes keep every image of `V`. -/
theorem JAtZV.agreeO (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {s' : S} {W : U64 → Prop}
    (hw : P1.WritesIn st s s' W) (hO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) :
    ∀ u ∈ V, VirtVcpuRel.AgreeAt (vmemW (L.mem s)) (vmemW (L.mem s')) u.bv :=
  v3_agreeW (L := L) hw (fun u hu => ((J.base.jvLay J.vm).vfit u hu).2) fun u hu b hb => J.oobj_v hu (hO b hb)

/-- At `V = ∅` a native step lifts, given that the spec state has no VCPU object. -/
theorem JAtZV3.of_native {Z' : XSets} {H' : P1.Heap} {Cs' Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64}
    {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (J' : JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σ')
    (R' : RunVmB (L := L) Z'.th s') (Vl' : VList st ∅ Z'.th s') (hO : VOnly ∅ σ') :
    JAtZV3 (L := L) arI ∅ ∅ AR Z' H' Cs' Ac' Lst' D' s' a' σ' :=
  ⟨JAtZV2.of_native J' R' Vl', hO, fun u hu => by simp at hu⟩

theorem JAtZV3.archV (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {a' : A}
    (hAR : AR a' σ.archState.x64CurrentCr3) : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a' σ :=
  ⟨J.z2.archV hAR, J.vo, J.vr⟩

/-- **`JAtZV2.ofB` at `JAtZV3`** (spec heap unchanged). -/
theorem JAtZV3.ofB (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ') {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) (hh : ∀ b, W b → b ≠ P1.vHeadA st s)
    (hv : VKeep (L := L) Z.th s s') (hke : σ'.kheap = σ.kheap) :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D' s' a' σ' :=
  ⟨J.z2.ofB B' hw hO hh hv hke, J.vo.frame fun p vs hp => by rw [← hke]; exact hp,
    J.vr.frame (fun u _ vs hu => by rw [← hke]; exact hu) (J.z2.zv.agreeO hw hO)⟩

/-- **`JAtZV2.ofBS` at `JAtZV3`**: one more argument, `hnv` (every VCPU object after was there, unchanged). -/
theorem JAtZV3.ofBS (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {Ac' : Set U64}
    {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ') {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) (hh : ∀ b, W b → b ≠ P1.vHeadA st s)
    (hv : VKeep (L := L) Z.th s s')
    (hvk : ∀ u ∈ V, σ'.kheap u.bv = σ.kheap u.bv)
    (hsz : ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko)
    (hrv : ∀ o x', σ'.kheap o = some (.tcb x') → x'.tcbState = .runningVM →
      ∃ x, σ.kheap o = some (.tcb x) ∧ x.tcbState = .runningVM)
    (hnv : ∀ p (vs : Fl4Spec.VcpuState), σ'.kheap p = some (.archObj (.vcpu vs)) →
      σ.kheap p = some (.archObj (.vcpu vs))) :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D' s' a' σ' :=
  ⟨J.z2.ofBS B' hw hO hh hv hvk hsz hrv, J.vo.frame hnv,
    J.vr.frame (fun u _ vs hu => hnv _ vs hu) (J.z2.zv.agreeO hw hO)⟩

/-- **The VM-epoch frame of an SC-code step at `JAtZV3`** (`JAtZV2.ofTK`, VCPU objects kept by `zv_tk_v`). -/
theorem JAtZV3.ofTK (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {Ac' : Set U64}
    {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ')
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw (fun _ => False) σ σ') :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D' s' a' σ' := by
  have hS := J.z2.zv.base.xtop.fin.1.1.1
  have hnv := zv_tk_v hK
  exact ⟨J.z2.ofTK B' hw hK, J.vo.frame hnv,
    J.vr.frame (fun u _ vs hu => hnv _ vs hu) (J.z2.zv.agreeO hw fun b hb => Sched.tfoot_oobj hS hb)⟩

/-- **`cancel_yield_to` at `JAtZV3`** (as `JAtZV2.cancelYieldJ`). -/
theorem JAtZV3.cancelYieldJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {y p : U64} (hy : y ∈ Z.T)
    (hp : L.mem s (yieldA y) = p) (hp0 : p ≠ 0#u64) :
    schedcontext.cancel_yield_to st s y ⦃ s' => ∃ σ',
      Fl4Spec.schedContextCancelYieldTo (Z := Unit) y.bv σ = ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64), JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D s' a σ' ⦄ :=
  WP.spec_mono (J.z2.zv.base.cancelYieldJD hy hp hp0) fun _ ⟨σ', he, hK, hW, Ac', Lst', B'⟩ =>
    ⟨σ', he, Ac', Lst', J.ofTK B' hW hK⟩

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 4000000 in
/-- **`possible_switch_to` at `JAtZV3 V X`** (P3/JAtZBSched2's `JAtZV2.switchJ`, the proof with `JAtZV3.ofB`). -/
theorem JAtZV3.switchJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (hti : t.bv ≠ σ.idleThread) (htc : t.bv ≠ σ.curThread) (hs : Fl4Spec.schedulable t.bv σ = true) :
    sched.possible_switch_to st s t ⦃ s' => ∃ σ', Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ Lst' : U64 → List U64, JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s' a σ' ⦄ := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hR := B.xtop.fin.1.1.2.2.1
  refine WP.spec_mono (WP.spec_and (WP.spec_and (B.switchJ ht hti htc hs)
    (possible_switch_to_refines s σ hR hS B.inv.actReady t ht)) (possible_switch_to_sfoot hR hS B.inv.actReady ht)) ?_
  rintro s' ⟨⟨⟨σ1, he1, Lst', B'⟩, ⟨σ2, he2, hke, -, -⟩⟩, hw⟩
  have e12 : σ2 = σ1 := by
    rw [he1] at he2
    have h := congrArg Prod.fst he2
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at h
    exact h.symm
  subst e12
  have hwT : P1.WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ) :=
    WritesIn.tfoot_of_kfoot (WritesIn.kfoot_of_sfoot hw)
  have hv : VKeep (L := L) Z.th s s' := VKeep.of_tfoot hS B.thT hwT
  have hh : ∀ b, SFoot st Z.T Z.c s b → b ≠ P1.vHeadA st s := by
    intro b hb e
    subst e
    have hvh : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val B.kern.ksbFit
    rcases SFoot.range hS.placed.tcb hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩
    · have d := B.kern.hks y _ (B.zH.1 y hy) (fun _ h => by cases h)
      simp only [P1.HKind.bits, Nat.reducePow] at d
      omega
    · have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
      omega
  exact ⟨σ2, he1, Lst', J.ofB B' hw (fun b h => tfoot_oobj hS (Or.inl (Or.inl h))) hh hv hke⟩

/-- **`Running` + `postpone` at `JAtZV3`** (P3/JAtZBRunPostV's `JAtZV2.runPostJ`, via `JAtZV3.ofBS`). -/
theorem JAtZV3.runPostJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (htD : t ∉ D)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .inactive)
    (htc : t.bv ≠ σ.curThread) {sc : U64} (hsc : sc ∈ Z.C) (hxsc : x.tcbSchedContext = some sc.bv)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hya : Fl4Spec.scActive y = true)
    (hnrel : ¬ (Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true ∧
      Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd y) = true)) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s6 =>
      sched.postpone st s6 sc ⦃ s7 => ∃ σ7, Fl4Spec.postpone (Z := Unit) sc.bv
          (stsAct (updK σ t.bv (.tcb { x with tcbState := .running })) t.bv) = ({((), σ7)}, False) ∧
        ∃ Lst' : U64 → List U64, JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s7 a σ7 ⦄ ⦄ := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  refine WP.spec_mono (B.runPostJV ht htD hk hrs htc hsc hxsc hky hya hnrel) fun s6 ⟨_, _, h6⟩ => ?_
  refine WP.spec_mono h6 fun s7 ⟨σ7, he, hW, hk7, hkp7, Lst', B'⟩ => ⟨σ7, he, Lst', ?_⟩
  refine J.ofBS B' hW (fun b hb => tfoot_oobj hS hb) (fun b hb => B.tfoot_nh hb) (VKeep.of_tfoot hS B.thT hW)
    (fun u hu => ?_) (fun o ko' ho => ?_) (fun o x' ho hx => ?_) (fun o vs ho => ?_)
  · obtain ⟨vu, hvu⟩ := J.z2.zv.vm.spec u hu
    refine hkp7 _ fun e => ?_
    rw [e, hk] at hvu; cases hvu
  · by_cases e : o = t.bv
    · subst e
      rw [hk7] at ho; cases ho
      exact ⟨_, hk, rfl⟩
    · rw [hkp7 _ e] at ho; exact ⟨ko', ho, rfl⟩
  · by_cases e : o = t.bv
    · subst e
      rw [hk7] at ho; cases ho
      cases hx
    · rw [hkp7 _ e] at ho; exact ⟨x', ho, hx⟩
  · by_cases e : o = t.bv
    · subst e
      rw [hk7] at ho; cases ho
    · rw [hkp7 _ e] at ho; exact ho

end

/-! ## VCPU-word writes -/

/-- **A write of an unread VCPU word keeps `JAtZV3`** (module docstring): offset in `[TCB, REGS)`, not a link word,
none of `XCR0`, `CR2`, `PENDING`, `VALID`, `VM_IBPB_DEFER` (e.g. `SVM_CPU`); the spec is unchanged. -/
theorem JAtZV3.vcpuWr (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p w : U64} (hp : p ∈ V)
    (hal : P1.Aligned w) (g1 : p.val ≤ w.val) (g2 : w.val < p.val + 32768)
    (hw : w.val ≠ p.val + 20480 ∧ w.val ≠ p.val + 20488 ∧ w.val ≠ p.val + 20496)
    (hun : 20480 ≤ w.val - p.val ∧ w.val - p.val < 20736 ∧ w.val - p.val ≠ 20504 ∧ w.val - p.val ≠ 20512 ∧
      w.val - p.val ≠ 20520 ∧ w.val - p.val ≠ 20528 ∧ w.val - p.val ≠ 20544) (x : U64) :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr s w x) a σ := by
  have Ly := J.z2.zv.base.jvLay J.z2.zv.vm
  have hW : P1.WritesIn st s (L.wr s w x) (· = w) := P1.writesIn_wr hal
  refine ⟨J.z2.vcpuWr hp hal g1 g2 hw x, J.vo, ?_⟩
  intro u hu vs hk
  have R0 := J.vr u hu vs hk
  have hfu := (Ly.vfit u hu).2
  by_cases e : u = p
  · rw [e] at R0 hfu ⊢
    obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := hun
    have ho0 : (BitVec.ofNat 64 (w.val - p.val)).toNat = w.val - p.val := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have ht : Fl4Spec.VcpuLay.TCB.toNat = 20480 := rfl
    refine v3_rel' (mem := vmemW (L.mem s)) (mem' := vmemW (L.mem (L.wr s w x)))
      (o0 := BitVec.ofNat 64 (w.val - p.val))
      (VUnread.ofRange (by rw [ho0]; omega) (by rw [ho0]; omega) (by rw [ho0]; omega) (by rw [ho0]; omega)
        (by rw [ho0]; omega) (by rw [ho0]; omega) (by rw [ho0]; omega))
      (v3_agree hfu fun b hb _ _ hne => hW.mem_eq hb fun e' => hne (by rw [e', ho0]; omega))
      (fun e' => hw.1 (by have h := congrArg BitVec.toNat e'; rw [ho0, ht] at h; omega)) R0
  · refine VirtVcpuRel.VcpuRel.congr (v3_agreeAll hfu fun b hb b1 b2 => hW.mem_eq hb fun e' => ?_) R0
    rw [e'] at b1 b2
    rcases Ly.vv u hu p hp e with h | h <;> omega

/-- **FL4's write of a non-link VCPU word paired with the spec's VCPU update** keeps `JAtZV3`, given the new
spec VCPU related to the new image (`hR`: the paired spec update, the caller's obligation). -/
theorem JAtZV3.vcpuStep (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p w : U64} (hp : p ∈ V)
    (hal : P1.Aligned w) (g1 : p.val ≤ w.val) (g2 : w.val < p.val + 32768)
    (hw : w.val ≠ p.val + 20480 ∧ w.val ≠ p.val + 20488 ∧ w.val ≠ p.val + 20496) (x : U64)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (vs' : Fl4Spec.VcpuState)
    (ht : Fl4Spec.VcpuState.tcb vs' = Fl4Spec.VcpuState.tcb vs)
    (hR : Fl4Spec.VcpuRel Fl4Spec.virtKind (vmemW (L.mem (L.wr s w x))) p.bv vs') :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr s w x) a (Notif.updK σ p.bv (.archObj (.vcpu vs'))) := by
  have Ly := J.z2.zv.base.jvLay J.z2.zv.vm
  have hW : P1.WritesIn st s (L.wr s w x) (· = w) := P1.writesIn_wr hal
  refine ⟨J.z2.vcpuStep hp hal g1 g2 hw x hk vs' ht, J.vo.updV hp _, J.vr.upd vs' hR fun u hu e => ?_⟩
  refine v3_agreeAll (Ly.vfit u hu).2 fun b hb b1 b2 => hW.mem_eq hb fun e' => ?_
  rw [e'] at b1 b2
  rcases Ly.vv u hu p hp e with h | h <;> omega

/-- **The spec's VCPU update alone** keeps `JAtZV3`, given the new spec VCPU related to FL4's image (`hR`). -/
theorem JAtZV3.vcpuSpec (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (vs' : Fl4Spec.VcpuState)
    (ht : Fl4Spec.VcpuState.tcb vs' = Fl4Spec.VcpuState.tcb vs)
    (hR : Fl4Spec.VcpuRel Fl4Spec.virtKind (vmemW (L.mem s)) p.bv vs') :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (Notif.updK σ p.bv (.archObj (.vcpu vs'))) :=
  ⟨J.z2.vcpuSpec hp hk vs' ht, J.vo.updV hp _, J.vr.upd vs' hR fun _ _ _ _ _ => rfl⟩

/-! ## Binding -/

set_option maxHeartbeats 4000000 in
/-- **`VRel` across the two link writes** (`v.TCB := x`, `t.VCPU := y`) with the spec VCPU's `tcb` set to
`vcpuTcbRef x`. -/
theorem JAtZV.vrelLink (Jz : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hr : VRel V σ (L.mem s))
    {t v : U64} (ht : Z.th t = some .tcb) (hv : v ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap v.bv = some (.archObj (.vcpu vs))) (x y : U64) :
    VRel V (Notif.updK σ v.bv (.archObj (.vcpu { vs with tcb := Fl4Spec.vcpuTcbRef x.bv })))
      (L.mem (L.wr (L.wr s (vTcbA v) x) (tVcpuA t) y)) := by
  have Ly := Jz.base.jvLay Jz.vm
  have hf := Ly.vfit v hv
  have hvt := lay_vTcb_val hf.2
  have halv : P1.Aligned (vTcbA v) := by unfold P1.Aligned; rw [hvt]; omega
  have hta := Ly.tA t ht
  have htv := lay_tVcpu_val hta
  have halt : P1.Aligned (tVcpuA t) := by unfold P1.Aligned; rw [htv]; have := hta.align; omega
  have hW := link_writes (st := st) (s := s) (x := x) (y := y) halv halt
  have htout : ∀ u ∈ V, (tVcpuA t).val < u.val ∨ u.val + 32768 ≤ (tVcpuA t).val := by
    intro u hu
    have d := Ly.vap u hu t _ ht
    simp only [objSize] at d
    omega
  have hm' : L.mem (L.wr (L.wr s (vTcbA v) x) (tVcpuA t) y) (vTcbA v) = x := by
    rw [L.mem_wr_ne halt halv ?_, L.mem_wr_same halv]
    intro e; rcases htout v hv with h | h <;> omega
  have hT : Fl4Spec.VcpuLay.TCB.toNat = 20480 := rfl
  have hm : ∀ b : U64, P1.Aligned b → v.val ≤ b.val → b.val < v.val + 32768 →
      b.val ≠ v.val + Fl4Spec.VcpuLay.TCB.toNat →
      L.mem (L.wr (L.wr s (vTcbA v) x) (tVcpuA t) y) b = L.mem s b := by
    intro b hb g1 g2 hne
    refine hW.mem_eq hb ?_
    rintro (rfl | rfl)
    · rw [hvt, hT] at hne; exact hne rfl
    · rcases htout v hv with h | h <;> omega
  refine VRel.upd hr _ ?_ fun u hu e => ?_
  · have R1 := v3_rel (mem := vmemW (L.mem s)) (mem' := vmemW (L.mem (L.wr (L.wr s (vTcbA v) x) (tVcpuA t) y)))
      (o0 := Fl4Spec.VcpuLay.TCB) VUnread.tcb (v3_agree hf.2 hm) (hr v hv vs hk)
    rw [v3_vmemW_tcb hf, hm'] at R1
    exact R1
  · refine v3_agreeAll (Ly.vfit u hu).2 fun b hb g1 g2 => hW.mem_eq hb ?_
    rintro (rfl | rfl)
    · rw [hvt] at g1 g2
      rcases Ly.vv u hu v hv e with h | h <;> omega
    · rcases htout u hu with h | h <;> omega

set_option maxHeartbeats 8000000 in
/-- **Binding at `JAtZV3`** (P3/JAtZBBind's `JAtZV2.bind`; the spec VCPU is `{ vs with tcb := some t }`, as
`associateVcpuTcb`'s last `vcpuUpdate` writes it). -/
theorem JAtZV3.bind (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t v : U64}
    (ht : Z.th t = some .tcb) (hv : v ∈ V) (hw0 : L.mem s (tVcpuA t) = 0#u64) (hb0 : L.mem s (vTcbA v) = 0#u64)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap v.bv = some (.archObj (.vcpu vs))) (vs' : Fl4Spec.VcpuState)
    (hvs : vs' = { vs with tcb := some t.bv }) :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr (L.wr s (vTcbA v) t) (tVcpuA t) v) a
      (Notif.updK σ v.bv (.archObj (.vcpu vs'))) := by
  have h0 : Z.th 0#u64 ≠ some .tcb := (J.z2.zv.base.detPl J.z2.zv.vm).h0
  have ht0 : t ≠ 0#u64 := fun e => h0 (by rw [← e]; exact ht)
  have ht0' : t.bv ≠ 0 := fun e => ht0 (UScalar.eq_of_val_eq (by show t.bv.toNat = (0#u64).bv.toNat; rw [e]; rfl))
  have er : Fl4Spec.vcpuTcbRef t.bv = some t.bv := by unfold Fl4Spec.vcpuTcbRef; rw [if_neg ht0']
  subst hvs
  refine ⟨J.z2.bind ht hv hw0 hb0 hk _ rfl, J.vo.updV hv _, ?_⟩
  have R := J.z2.zv.vrelLink J.vr ht hv hk t v
  rw [er] at R
  exact R

set_option maxHeartbeats 8000000 in
/-- **Unbinding at `JAtZV3`** (P3/JAtZBBind's `JAtZV2.unbind`; the spec VCPU is `{ vs with tcb := none }`, as
`vcpuDetach`'s last `vcpuUpdate` writes it). -/
theorem JAtZV3.unbind (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t v : U64}
    (ht : Z.th t = some .tcb) (hv : v ∈ V) (htv : L.mem s (tVcpuA t) = v) (hvt : L.mem s (vTcbA v) = t)
    (hst : L.mem s (P1.stA t) ≠ 8#u64)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap v.bv = some (.archObj (.vcpu vs))) (vs' : Fl4Spec.VcpuState)
    (hvs : vs' = { vs with tcb := none }) :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr (L.wr s (vTcbA v) 0#u64) (tVcpuA t) 0#u64) a
      (Notif.updK σ v.bv (.archObj (.vcpu vs'))) := by
  have er : Fl4Spec.vcpuTcbRef (0#u64).bv = none := by unfold Fl4Spec.vcpuTcbRef; exact if_pos (by decide)
  subst hvs
  refine ⟨J.z2.unbind ht hv htv hvt hst hk _ rfl, J.vo.updV hv _, ?_⟩
  have R := J.z2.zv.vrelLink J.vr ht hv hk 0#u64 0#u64
  rw [er] at R
  exact R

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit Classical

/-- **The boot witness's spec state has no VCPU object.** -/
theorem vonly_σ1 : VOnly ∅ σ1 := by
  intro p vs hk
  exfalso
  rcases kh1_some hk with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, -, h⟩
  · cases e
  · cases e
  · cases e
  · rcases fInit_objs (p := p) h with e | e | e | e | e | e <;> cases e

/-- **`JAtZV3 ∅ ∅` at the boot witness `w1`** (no premise). -/
theorem jAtZV3_w1 (a : MachineState) :
    JAtZV3 (L := wL) warI ∅ ∅ wAR Zw1 Hw1 Csw C1 (fun _ => []) Dw w1 a σ1 :=
  ⟨jAtZV2_w1 a, vonly_σ1, fun u hu => by simp at hu⟩

end Fl4Proofs.P3.JBoot
