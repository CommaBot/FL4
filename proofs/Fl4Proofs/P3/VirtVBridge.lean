/-
P3x for virtualization (line virt, gen 21, item 2): **per-step bridges to `VRelAll`** — gen 20's plan step 1: from
the footprint forms the existing native step proofs state to VirtVKeep's `VRelAll.of_writes`, so a native step with
such a footprint and a spec side leaving the VCPU objects alone keeps the VCPU relation over the whole VCPU set.

## The FL4 side: footprint classes off every VCPU

The existing native proofs state their FL4 writes as `P1.WritesIn s s' W` (or UntypedFrameBase's `WFrame`, the
same shape: `WritesIn.of_wframe`) with `W` inside one of these classes; each is shown off every VCPU of `V`
(`OffV V`, aligned words), from the placement records `JVLay V th U` / `JVm V H s σ` / `P1.HeapOK H` and the
membership of the relation's object sets:

* `offV_heap`: a word inside a non-`.other` object of the P1 heap `H` (`HeapOK.disj` against `JVm.heap`: a VCPU is
  `.other 15`); `offV_spec`: a word inside a non-VCPU spec object (`JVm.sep`); `offV_ksA`: a word of the
  kernel-global area `[ksb, ksb + 304384)` (`JVm.ks`); `offV_objA`: a word inside a typed-heap object
  (`JVLay.vap`).
* **`offV_oobj`**: VsTop's `OObj` (the IPC / scheduler / notification / SC / buffer words: the core's node, the
  kernel-state block, TCB words `t + [256, 4096)`, endpoints, replies, notifications, SC objects, buffer words),
  given `T`/`E`/`R`/`N` objects of `H` of their kinds, the buffer words in `U`, the core below 64.
* **`offV_vobj`**: VsTop's `VObj` (CNode and TCB-slot words of `th`, page-table pages, the ASID block
  `[ksb + 288000, ksb + 304384)`), given the page-table pages apart from `V` (`hPg`).
* **`offV_xfer`** (P1's `XferFoot`: message transfers, `vcpu.report`'s `RepW` is the same shape: `offV_repW`), TCBs
  of `T` objects of `H`.
* **`VRelAll.of_native`**: a `WritesIn` footprint inside `OObj ∪ VObj ∪ XferFoot` + the spec side keeping every
  `vcpuAt` on `V` ⇒ `VRelAll` kept; `VRelAll.of_wframe` (the same through `WFrame`).

## The spec side

* `vcpuAt_of_pt`: a spec step where every heap entry is unchanged or was not a VCPU keeps `vcpuAt` on `V`
  (`V` VCPU objects of the pre-state, `JVm.spec`); instances **`vcpuAt_ntfnStep`** (NtfnRel's `NtfnStep`: the
  notification code) and **`vcpuAt_epStep`** (EpRel's `EpStep`: the endpoint code); VirtVKeep's `vcpuAt_updK` /
  `vcpuAt_ofKheap` cover in-place updates and heap-preserving steps.
* **`VRelAll.of_ntfnStep`**, **`VRelAll.of_epStep`**: the two IPC step shapes with an `OObj ∪ VObj ∪ XferFoot`
  footprint keep `VRelAll`.

## Footprints too coarse for this bridge (found here; handoff gen 21)

* `untyped.reset_untyped` (UntypedFrame `ResetW p sb x PW`: the whole untyped region): a VCPU retyped from that
  untyped whose cap was deleted (object left in the heap, l4v keeps it until detype) lies inside the region, and
  the reset zeroes it. Not a gap in the statement but a different shape: the spec's `detype` removes those VCPUs,
  so the post relation is over `V \ region` (`VRelAll.mono`), not `V`.
* Steps whose only memory fact is an agreement on the words some relation reads (EpTail's `FootEq`, `Agree … IFoot`,
  NtfnRel's `FootEq`) say nothing about the other words; they need their `WritesIn` (where the step proof has one
  inside, e.g. IpcSlotsSame's `hWO`) to reach `VRelAll`.

No premise (no [J]/[P]/[W]): every hypothesis is a state, placement or footprint fact. New file only; no existing
statement changed.
-/
import Fl4Proofs.P3.VirtVKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtVBridge
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit
open Fl4Proofs.P3.VirtReplyKeep Fl4Proofs.P3.VirtDispVcpu Fl4Proofs.P3.VirtVKeep

noncomputable section

theorem VRelAll.mono {Z : Type} {V V' : Set U64} (h : V' ⊆ V) {mem : Word → Word} {σ : State Z}
    (hR : VRelAll V mem σ) : VRelAll V' mem σ := fun v hv => hR v (h hv)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- `WFrame` (UntypedFrameBase) is a `WritesIn` footprint. -/
theorem WritesIn.of_wframe {s s' : S} {P : U64 → Prop} (h : WFrame (L := L) s s' P) : P1.WritesIn st s s' P :=
  ⟨h.1, h.2.1, fun b hb hn => h.2.2 b hb hn⟩

variable {V : Set U64} {H : P1.Heap} {s : S} {σ : State Unit}

/-- A word inside a non-`.other` object of the P1 heap is off `V`'s VCPUs. -/
theorem offV_heap (Hk : P1.HeapOK H) (J : JVm (L := L) V H s σ) (hf : ∀ v ∈ V, VFits v) {p : U64}
    {k : P1.HKind} (hp : H p = some k) (hk : ∀ z, k ≠ .other z) {b : U64} (hb : b.val % 8 = 0)
    (h1 : p.val ≤ b.val) (h2 : b.val < p.val + 2 ^ k.bits) : OffV V b := fun v hv => by
  have hne : p ≠ v := fun e => by
    subst e
    rw [J.heap p hv] at hp
    exact hk 15 (Option.some.inj hp).symm
  have hv1 := (hf v hv).1
  have e15 : (2 : Nat) ^ 15 = 32768 := by norm_num
  rcases Hk.disj p k v (.other 15) hp (J.heap v hv) hne with c | c
  · left; omega
  · right; simp only [P1.HKind.bits, e15] at c; omega

/-- A word inside a non-VCPU spec object is off `V`'s VCPUs. -/
theorem offV_spec (J : JVm (L := L) V H s σ) (hf : ∀ v ∈ V, VFits v) {p : U64} {ko : KernelObject}
    (hp : σ.kheap p.bv = some ko) (hnv : ∀ x, ko ≠ .archObj (.vcpu x)) {b : U64} (hb : b.val % 8 = 0)
    (h1 : p.val ≤ b.val) (h2 : b.val < p.val + 2 ^ objBits ko) : OffV V b := fun v hv => by
  have hne := J.ne_of hp hnv v hv
  have ha := J.sep v hv p.bv ko hp hne
  have hv1 := (hf v hv).1
  have e : p.bv.toNat = p.val := rfl
  unfold VcpuApart at ha
  rw [e] at ha
  rcases ha with c | c
  · left; omega
  · right; omega

/-- A word of the kernel-global area is off `V`'s VCPUs. -/
theorem offV_ksA (J : JVm (L := L) V H s σ) (hf : ∀ v ∈ V, VFits v) {b : U64} (hb : b.val % 8 = 0)
    (h1 : (L.ksb s).val ≤ b.val) (h2 : b.val < (L.ksb s).val + 304384) : OffV V b := fun v hv => by
  have hv1 := (hf v hv).1
  rcases J.ks v hv with c | c
  · right; omega
  · left; omega

end

section
variable {V : Set U64} {th : TypedHeap} {U : Set U64}

/-- A word inside a typed-heap object is off `V`'s VCPUs (strict upper bound, aligned word). -/
theorem offV_objA (Ly : JVLay V th U) {p : U64} {k : ObjKind} (hp : th p = some k) {b : U64} (hb : b.val % 8 = 0)
    (h1 : p.val ≤ b.val) (h2 : b.val < p.val + objSize k) : OffV V b := fun v hv => by
  have hv1 := (Ly.vfit v hv).1
  rcases Ly.vap v hv p k hp with c | c
  · left; omega
  · right; omega

end

/-! ## The footprint classes -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {V : Set U64} {H : P1.Heap} {s : S} {σ : State Unit} {th : TypedHeap} {U : Set U64}

theorem bits_tcb : (2 : Nat) ^ P1.HKind.tcb.bits = 4096 := by simp [P1.HKind.bits]
theorem bits_ep : (2 : Nat) ^ P1.HKind.ep.bits = 16 := by simp [P1.HKind.bits]
theorem bits_ntfn : (2 : Nat) ^ P1.HKind.ntfn.bits = 64 := by simp [P1.HKind.bits]
theorem bits_reply : (2 : Nat) ^ P1.HKind.reply.bits = 32 := by simp [P1.HKind.bits]

/-- **VsTop's `OObj` words are off `V`'s VCPUs** (module docstring). -/
theorem offV_oobj (Ly : JVLay V th U) (Hk : P1.HeapOK H) (J : JVm (L := L) V H s σ) {N T C E R : Set U64}
    {B : Set (U64 × Word)} {c : U64} (hc : c.val < 64) (hT : ∀ t ∈ T, H t = some .tcb)
    (hE : ∀ e ∈ E, H e = some .ep) (hR : ∀ r ∈ R, H r = some .reply) (hN : ∀ n ∈ N, H n = some .ntfn)
    (hB : ∀ wp ∈ B, wp.1 ∈ U) {b : U64} (hb : P1.Aligned b) (h : Vs.OObj st N T C E R B c s σ b) : OffV V b := by
  have hf : ∀ v ∈ V, VFits v := Ly.vfit
  have hb8 : b.val % 8 = 0 := hb
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, -⟩ | ⟨t, ht, h1, h2⟩ | ⟨e, he, h1, h2⟩ | ⟨r, hr, h1, h2⟩ | ⟨n, hn, h1, h2⟩ |
      ⟨sc, -, x, n, hk, hsc⟩ | ⟨wp, hwp, h1, h2⟩
  · unfold P1.LawfulStore.nodeBase at h1 h2
    have : c.val * 4288 ≤ 63 * 4288 := Nat.mul_le_mul_right _ (by omega)
    exact offV_ksA J hf hb8 (by omega) (by omega)
  · exact offV_ksA J hf hb8 h1 (by omega)
  · exact offV_heap Hk J hf (hT t ht) (fun z h => by cases h) hb8 (by omega) (by rw [bits_tcb]; omega)
  · exact offV_heap Hk J hf (hE e he) (fun z h => by cases h) hb8 h1 (by rw [bits_ep]; omega)
  · exact offV_heap Hk J hf (hR r hr) (fun z h => by cases h) hb8 h1 (by rw [bits_reply]; omega)
  · exact offV_heap Hk J hf (hN n hn) (fun z h => by cases h) hb8 h1 (by rw [bits_ntfn]; omega)
  · refine offV_spec J hf hk (fun y h => by cases h) hb8 hsc.1 ?_
    have h2 := hsc.2
    have e2 : Fl4Spec.minSchedContextBits + n = n + Fl4Spec.minSchedContextBits := Nat.add_comm _ _
    simp only [Fl4Spec.objBits]
    rw [e2]; exact h2
  · have hw := Ly.ua _ (hB wp hwp)
    have hw8 : wp.1.val % 8 = 0 := hw
    have e : b = wp.1 := UScalar.eq_of_val_eq (by omega)
    rw [e]; exact offV_U Ly (hB wp hwp)

theorem offV_vobj_cn (Ly : JVLay V th U) {q : U64} {r : Nat} (hq : th q = some (.cnode r)) {b : U64}
    (hb8 : b.val % 8 = 0) (h1 : q.val ≤ b.val) (h2 : b.val < q.val + 32 * 2 ^ r) : OffV V b :=
  offV_objA Ly hq hb8 h1 (by simp only [objSize]; exact h2)

theorem offV_vobj_tcb (Ly : JVLay V th U) {t : U64} (ht : th t = some .tcb) {b : U64}
    (hb8 : b.val % 8 = 0) (h1 : t.val ≤ b.val) (h2 : b.val < t.val + 192) : OffV V b :=
  offV_objA Ly ht hb8 h1 (by simp only [objSize]; omega)

theorem offV_vobj_pg (Ly : JVLay V th U) {q : U64} (hq : ∀ v ∈ V, q.val + 4096 ≤ v.val ∨ v.val + 32768 ≤ q.val)
    {b : U64} (hb8 : b.val % 8 = 0) (h1 : q.val ≤ b.val) (h2 : b.val < q.val + 4096) : OffV V b := by
  intro v hv
  have hv1 := (Ly.vfit v hv).1
  rcases hq v hv with c | c
  · left; omega
  · right; omega

set_option maxRecDepth 100000 in
theorem offV_vobj_as (Ly : JVLay V th U) (J : JVm (L := L) V H s σ) {b : U64} (hb8 : b.val % 8 = 0)
    (h1 : (L.ksb s).val + 288000 ≤ b.val) (h2 : b.val < (L.ksb s).val + 288000 + 16384) : OffV V b := fun v hv => by
  have hv1 := (Ly.vfit v hv).1
  have hk := J.ks v hv
  generalize (L.ksb s).val = K at h1 h2 hk
  rcases hk with c | c
  · right; omega
  · left; omega

/-- **VsTop's `VObj` words are off `V`'s VCPUs** (module docstring; `hPg`: the page-table pages apart from `V`). -/
theorem offV_vobj (Ly : JVLay V th U) (J : JVm (L := L) V H s σ) {P L4 L3 L2 L1 : Set U64}
    (hPg : ∀ q, (q ∈ P ∨ q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) → ∀ v ∈ V,
      q.val + 4096 ≤ v.val ∨ v.val + 32768 ≤ q.val)
    {b : U64} (hb : P1.Aligned b) (h : Vs.VObj th P L4 L3 L2 L1 (L.ksb s) b) : OffV V b := by
  have hb8 : b.val % 8 = 0 := hb
  rcases h with ⟨q, r, hq, h1, h2⟩ | ⟨t, ht, h1, h2⟩ | ⟨q, hq, h1, h2⟩ | ⟨h1, h2⟩
  · exact offV_vobj_cn Ly hq hb8 h1 h2
  · exact offV_vobj_tcb Ly ht hb8 h1 h2
  · exact offV_vobj_pg Ly (hPg q hq) hb8 h1 h2
  · exact offV_vobj_as Ly J hb8 h1 h2

/-- A TCB word `y + K` (`K < 4096`) of a P1-heap TCB `y` is off `V`'s VCPUs. -/
theorem offV_tcbH (Hk : P1.HeapOK H) (J : JVm (L := L) V H s σ) (hf : ∀ v ∈ V, VFits v) {y : U64}
    (hy : H y = some .tcb) {K : U64} (hK : K.val < 4096) (hK8 : K.val % 8 = 0) :
    OffV V (core.num.U64.wrapping_add y K) := by
  have hfit := Hk.fits y _ hy
  have hal := Hk.align y _ hy
  rw [bits_tcb] at hfit hal
  have e : (core.num.U64.wrapping_add y K).val = y.val + K.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  exact offV_heap Hk J hf hy (fun z h => by cases h) (by rw [e]; omega) (by rw [e]; omega)
    (by rw [e, bits_tcb]; omega)

/-- **P1's `XferFoot` words are off `V`'s VCPUs** (message transfers; `T` objects of `H` are TCBs). -/
theorem offV_xfer (Ly : JVLay V th U) (Hk : P1.HeapOK H) (J : JVm (L := L) V H s σ) {T : Set U64}
    (hT : ∀ t ∈ T, H t = some .tcb) {b : U64} (h : P1.XferFoot T U b) : OffV V b := by
  rcases h with ⟨y, hy, K, hK, hK8, rfl⟩ | hu
  · exact offV_tcbH Hk J Ly.vfit (hT y hy) (by omega) hK8
  · exact offV_U Ly hu

/-- **`P1.RepW t U` words are off `V`'s VCPUs** (`vcpu.report`, the error reply). -/
theorem offV_repW (Ly : JVLay V th U) (Hk : P1.HeapOK H) (J : JVm (L := L) V H s σ) {t : U64}
    (ht : H t = some .tcb) {b : U64} (h : P1.RepW t U b) : OffV V b := by
  rcases h with ⟨K, -, hK, hK8, rfl⟩ | hu
  · exact offV_tcbH Hk J Ly.vfit ht (by omega) hK8
  · exact offV_U Ly hu

/-! ## Whole steps -/

variable {Z : Type}

/-- **A native step whose footprint is inside `OObj ∪ VObj ∪ XferFoot` keeps `VRelAll`** (module docstring). -/
theorem VRelAll.of_native (Ly : JVLay V th U) (Hk : P1.HeapOK H) (J : JVm (L := L) V H s σ)
    {N T C E R : Set U64} {B : Set (U64 × Word)} {c : U64} (hc : c.val < 64) (hT : ∀ t ∈ T, H t = some .tcb)
    (hE : ∀ e ∈ E, H e = some .ep) (hR : ∀ r ∈ R, H r = some .reply) (hN : ∀ n ∈ N, H n = some .ntfn)
    (hB : ∀ wp ∈ B, wp.1 ∈ U) {P L4 L3 L2 L1 : Set U64}
    (hPg : ∀ q, (q ∈ P ∨ q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) → ∀ v ∈ V,
      q.val + 4096 ≤ v.val ∨ v.val + 32768 ≤ q.val)
    {s' : S} {σ0 σ' : State Z} (h : VRelAll V (memW st s) σ0) {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → Vs.OObj st N T C E R B c s σ b ∨ Vs.VObj th P L4 L3 L2 L1 (L.ksb s) b ∨ P1.XferFoot T U b)
    (hs : ∀ v ∈ V, vcpuAt σ' v.bv = vcpuAt σ0 v.bv) : VRelAll V (memW st s') σ' :=
  VRelAll.of_writes Ly.vfit h hw (fun b hb ha => by
    rcases hW b hb with h1 | h1 | h1
    · exact offV_oobj Ly Hk J hc hT hE hR hN hB ha h1
    · exact offV_vobj Ly J hPg ha h1
    · exact offV_xfer Ly Hk J hT h1) hs

/-- `VRelAll.of_native` through UntypedFrameBase's `WFrame`. -/
theorem VRelAll.of_wframe (Ly : JVLay V th U) (Hk : P1.HeapOK H) (J : JVm (L := L) V H s σ)
    {N T C E R : Set U64} {B : Set (U64 × Word)} {c : U64} (hc : c.val < 64) (hT : ∀ t ∈ T, H t = some .tcb)
    (hE : ∀ e ∈ E, H e = some .ep) (hR : ∀ r ∈ R, H r = some .reply) (hN : ∀ n ∈ N, H n = some .ntfn)
    (hB : ∀ wp ∈ B, wp.1 ∈ U) {P L4 L3 L2 L1 : Set U64}
    (hPg : ∀ q, (q ∈ P ∨ q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) → ∀ v ∈ V,
      q.val + 4096 ≤ v.val ∨ v.val + 32768 ≤ q.val)
    {s' : S} {σ0 σ' : State Z} (h : VRelAll V (memW st s) σ0) {W : U64 → Prop} (hw : WFrame (L := L) s s' W)
    (hW : ∀ b, W b → Vs.OObj st N T C E R B c s σ b ∨ Vs.VObj th P L4 L3 L2 L1 (L.ksb s) b ∨ P1.XferFoot T U b)
    (hs : ∀ v ∈ V, vcpuAt σ' v.bv = vcpuAt σ0 v.bv) : VRelAll V (memW st s') σ' :=
  VRelAll.of_native Ly Hk J hc hT hE hR hN hB hPg h (WritesIn.of_wframe hw) hW hs

end

/-! ## The spec side -/

section
variable {Z : Type} {V : Set U64}

/-- A spec step where every heap entry is unchanged or was not a VCPU keeps `vcpuAt` on `V`'s VCPUs. -/
theorem vcpuAt_of_pt {σ σ' : State Z} (hV : ∀ v ∈ V, ∃ x, σ.kheap v.bv = some (.archObj (.vcpu x)))
    (h : ∀ p, σ'.kheap p = σ.kheap p ∨ ∀ x, σ.kheap p ≠ some (.archObj (.vcpu x))) :
    ∀ v ∈ V, vcpuAt σ' v.bv = vcpuAt σ v.bv := by
  intro v hv
  obtain ⟨x, hx⟩ := hV v hv
  rcases h v.bv with e | e
  · unfold vcpuAt; rw [e]
  · exact absurd hx (e x)

/-- **The notification code's spec step keeps every VCPU** (NtfnRel's `NtfnStep`). -/
theorem vcpuAt_ntfnStep {σ σ' : State Z} (hV : ∀ v ∈ V, ∃ x, σ.kheap v.bv = some (.archObj (.vcpu x)))
    (h : Notif.NtfnStep σ σ') : ∀ v ∈ V, vcpuAt σ' v.bv = vcpuAt σ v.bv :=
  vcpuAt_of_pt hV fun p => (h.2.2 p).imp id fun h' x e => by
    rcases h' with ⟨a, b, ha, -⟩ | ⟨a, b, ha, -⟩ <;> rw [ha] at e <;> simp at e

/-- **The endpoint code's spec step keeps every VCPU** (EpRel's `EpStep`). -/
theorem vcpuAt_epStep {σ σ' : State Z} (hV : ∀ v ∈ V, ∃ x, σ.kheap v.bv = some (.archObj (.vcpu x)))
    (h : Endp.EpStep σ σ') : ∀ v ∈ V, vcpuAt σ' v.bv = vcpuAt σ v.bv :=
  vcpuAt_of_pt hV fun p => (h.2.2 p).imp id fun h' x e => by
    rcases h' with ⟨a, b, ha, -⟩ | ⟨a, b, ha, -⟩ | ⟨a, b, ha, -⟩ <;> rw [ha] at e <;> simp at e

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {V : Set U64} {H : P1.Heap} {s : S} {σ : State Unit} {th : TypedHeap} {U : Set U64}

/-- **The notification code's steps keep `VRelAll`** (footprint inside `OObj ∪ VObj ∪ XferFoot`, `NtfnStep`). -/
theorem VRelAll.of_ntfnStep (Ly : JVLay V th U) (Hk : P1.HeapOK H) (J : JVm (L := L) V H s σ)
    {N T C E R : Set U64} {B : Set (U64 × Word)} {c : U64} (hc : c.val < 64) (hT : ∀ t ∈ T, H t = some .tcb)
    (hE : ∀ e ∈ E, H e = some .ep) (hR : ∀ r ∈ R, H r = some .reply) (hN : ∀ n ∈ N, H n = some .ntfn)
    (hB : ∀ wp ∈ B, wp.1 ∈ U) {P L4 L3 L2 L1 : Set U64}
    (hPg : ∀ q, (q ∈ P ∨ q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) → ∀ v ∈ V,
      q.val + 4096 ≤ v.val ∨ v.val + 32768 ≤ q.val)
    {s' : S} {σ' : State Unit} (h : VRelAll V (memW st s) σ) {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → Vs.OObj st N T C E R B c s σ b ∨ Vs.VObj th P L4 L3 L2 L1 (L.ksb s) b ∨ P1.XferFoot T U b)
    (hst : Notif.NtfnStep σ σ') : VRelAll V (memW st s') σ' :=
  VRelAll.of_native Ly Hk J hc hT hE hR hN hB hPg h hw hW (vcpuAt_ntfnStep J.spec hst)

/-- **The endpoint code's steps keep `VRelAll`** (footprint inside `OObj ∪ VObj ∪ XferFoot`, `EpStep`). -/
theorem VRelAll.of_epStep (Ly : JVLay V th U) (Hk : P1.HeapOK H) (J : JVm (L := L) V H s σ)
    {N T C E R : Set U64} {B : Set (U64 × Word)} {c : U64} (hc : c.val < 64) (hT : ∀ t ∈ T, H t = some .tcb)
    (hE : ∀ e ∈ E, H e = some .ep) (hR : ∀ r ∈ R, H r = some .reply) (hN : ∀ n ∈ N, H n = some .ntfn)
    (hB : ∀ wp ∈ B, wp.1 ∈ U) {P L4 L3 L2 L1 : Set U64}
    (hPg : ∀ q, (q ∈ P ∨ q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) → ∀ v ∈ V,
      q.val + 4096 ≤ v.val ∨ v.val + 32768 ≤ q.val)
    {s' : S} {σ' : State Unit} (h : VRelAll V (memW st s) σ) {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → Vs.OObj st N T C E R B c s σ b ∨ Vs.VObj th P L4 L3 L2 L1 (L.ksb s) b ∨ P1.XferFoot T U b)
    (hst : Endp.EpStep σ σ') : VRelAll V (memW st s') σ' :=
  VRelAll.of_native Ly Hk J hc hT hE hR hN hB hPg h hw hW (vcpuAt_epStep J.spec hst)

end

end
end Fl4Proofs.P3.VirtVBridge
