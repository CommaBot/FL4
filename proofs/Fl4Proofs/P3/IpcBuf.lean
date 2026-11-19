/-
P3 (DESIGN.md §9), IPC: **the IPC buffers** (`EpBufHyps`, `EpBufMapHyps`).

FL4's `lookup_ipc_buffer` reads the TCB's IPC-buffer word (`t + 3512`,
`tcb::IPC_BUFFER`) and the cap in its buffer slot (slot 2); l4v's
`lookup_ipc_buffer` (`ipcBufOf`) reads `tcb_ipcframe` (the same slot, by
`tcb_cnode_map`) and `tcb_ipc_buffer`.

* `BufWordRel`: the IPC-buffer word is the spec's `tcb_ipc_buffer`, for the
  TCBs of `T`; `BufWordRel.frame`: kept by any step that writes no `t + 3512`
  and keeps every TCB's `tcb_ipc_buffer` (both in IpcTopFrame; `VsP.bw` carries it).
* `IpcBufCapOK` (l4v `valid_cap`, `valid_ipc_buffer_cap`): a buffer cap with
  read rights is of a non-device frame at a nonzero address aligned to its
  size, the buffer pointer is aligned to the buffer size, and the buffer's
  128 words lie in user frames (`inUserFrame`, what `copy_mrs` and
  `get_receive_slots` test). Not an existing data page at the cap's own
  pointer and size, as l4v's `valid_cap` (`typ_at AUserData`) has it: FL4's
  `Page_DeriveSubframe` (Ext/VSpace) makes 4 KiB caps inside a large page
  that name no object of their own, and SetIPCBuffer accepts them.
  **Device frames:** l4v's abstract `lookup_ipc_buffer` (`ipcBufOf`) does
  not test the frame's device flag, while FL4 and C seL4
  (`lookupIPCBuffer`, `cap_frame_cap_get_capFIsDevice`) return no buffer
  for one; seL4's `checkValidIPCBuffer` (TCB SetIPCBuffer) rejects device
  frames, so the two agree only under this invariant, which the final fold
  must establish.
* `BufCover` (a ghost-set placement fact): the tracked buffer words `B`
  include every TCB's buffer.
* `lookup_buf_rel`: `EpBufHyps.lookup` (FL4's address is 0 exactly when the
  spec has no buffer) from the CSpace relation and `IpcBufCapOK`.
-/
import Fl4Proofs.P3.IpcLeaves
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Words
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem obj.Tcb.ipc_buffer.spec' (s : S) (t : obj.Tcb) :
    obj.Tcb.ipc_buffer st t s ⦃ v => v = L.mem s (tIpcBufA t) ⦄ := by
  unfold obj.Tcb.ipc_buffer layout.tcb.IPC_BUFFER; step*
  obtain rfl : i = 3512#u64 := UScalar.eq_of_val_eq (by simpa using i_post)
  simp_all [tIpcBufA]

theorem tcb_slot_buffer (t : U64) : obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok (slotOf t 2) := by
  unfold obj.Tcb.slot layout.tcb.SLOT_BUFFER layout.cte.SIZE
  simp only [lift, bind_ok]
  congr 1

end Words

section Defs
open Fl4Spec

/-- **The IPC-buffer caps** (module docstring; l4v `valid_cap`,
`valid_ipc_buffer_cap`). -/
def IpcBufCapOK (σ : State Unit) : Prop :=
  ∀ t x, σ.kheap t = some (.tcb x) → ∀ dev p R mt vms md,
    x.tcbIpcframe = .archObjectCap (.pageCap dev p R mt vms md) → vmReadOnly ⊆ R →
    dev = false ∧ p ≠ 0 ∧
      (∀ k, k < 128 → inUserFrame (bufAddr (p + (x.tcbIpcBuffer &&& mask (pageBitsForSize vms))) k) σ) ∧
      x.tcbIpcBuffer.toNat % 1024 = 0 ∧
      p.toNat % 2 ^ pageBitsForSize vms = 0

/-- **The tracked buffer words cover the IPC buffers** (a ghost-set placement
fact, as `IPlaced`): every buffer the spec finds for a TCB of `T` is mapped
in `B` at its own address. -/
def BufCover (T : Set U64) (B : Set (U64 × Word)) (σ : State Unit) : Prop :=
  ∀ t ∈ T, ∀ x b p, σ.kheap t.bv = some (.tcb x) → Endp.ipcBufOf b x = some p → ∀ w : U64, w.bv = p →
    Endp.BufMap B w p

end Defs

section Lookup
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- The buffer slot of a related TCB: FL4's cap and the spec's. -/
theorem _root_.Fl4Proofs.P3.StateRel.bufCap {Z : Type} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Z}
    (hR : StateRel th (L.mem s) σ) {t : U64} (ht : th t = some .tcb) :
    ∃ x c, σ.kheap t.bv = some (.tcb x) ∧ capAt (L.mem s) (slotOf t 2) = ok c ∧ CapRel c x.tcbIpcframe := by
  obtain ⟨x, hkx, hsl⟩ := hR.tcb t ht
  obtain ⟨c, ac, hc, hac, hca⟩ := hsl 2 (by decide)
  rw [tcbCnodeMap_two] at hac
  cases hac
  exact ⟨x, c, hkx, hc, hca⟩

theorem vmRights_rw {r : U64} : Fl4Spec.vmReadWrite ⊆ vmRightsOf r ↔ r.val = 3 := by
  unfold vmRightsOf Fl4Spec.vmReadWrite Fl4Spec.vmReadOnly Fl4Spec.vmKernelOnly
  split_ifs with h3 h2
  · simp [h3]
  · simp [h3, Set.subset_def]
  · simp only [h3, iff_false]; intro h; exact absurd (h (by simp : Fl4Spec.Rights.allowRead ∈ _)) (by simp)

theorem vmRights_ro {r : U64} : Fl4Spec.vmReadOnly ⊆ vmRightsOf r ↔ (r.val = 3 ∨ r.val = 2) := by
  unfold vmRightsOf Fl4Spec.vmReadWrite Fl4Spec.vmReadOnly Fl4Spec.vmKernelOnly
  split_ifs with h3 h2
  · simp [h3, Set.subset_def]
  · simp [h2, Set.subset_def]
  · simp [h3, h2, Set.subset_def]

/-- **The buffer address of a frame**: `ptr + (w & (2 ^ bits - 1))`, without
wrapping (the frame aligned to its size). -/
theorem frame_off_spec (sz : capability.FrameSize) (p w : U64) (hal : p.val % 2 ^ frameBitsN sz = 0) :
    (do
      let bits ← capability.FrameSize.bits sz
      let i ← lift (bits &&& 63#u64)
      let i1 ← 1#u64 <<< i
      let i2 ← lift (core.num.U64.wrapping_sub i1 1#u64)
      let i3 ← lift (w &&& i2)
      ok (core.num.U64.wrapping_add p i3)) ⦃ v => v.val = p.val + w.val % 2 ^ frameBitsN sz ⦄ := by
  have hp := p.hBounds
  have hw := w.hBounds
  cases sz <;> simp only [capability.FrameSize.bits, bind_ok] <;> step* <;>
  · simp only [frameBitsN] at hal ⊢
    have hi : i.val = _ := i_post
    simp only [UScalar.val_and] at hi i3_post
    rw [core.num.U64.wrapping_add_val_eq]
    norm_num at hi
    rw [hi] at i1_post
    have h2 : i2.val = i1.val - 1 := by
      have h1 : (1#u64 : U64).val = 1 := rfl
      rw [i2_post, core.num.U64.wrapping_sub_val_eq, h1]; simp only [UScalar.size, UScalarTy.numBits] at *; omega
    rw [h2, i1_post, Nat.and_two_pow_sub_one_eq_mod] at i3_post
    rw [i3_post]
    simp only [UScalar.size, UScalarTy.numBits] at *
    omega

theorem frame_mask_toNat (sz : capability.FrameSize) (tb : BitVec 64) :
    (tb &&& Fl4Spec.mask (Fl4Spec.pageBitsForSize (frameSizeOf sz))).toNat = tb.toNat % 2 ^ frameBitsN sz := by
  have h : ∀ k : Nat, k < 64 → (Fl4Spec.mask k : BitVec 64).toNat = 2 ^ k - 1 := by
    intro k hk
    have : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hk
    have h1 : 0 < 2 ^ k := by positivity
    unfold Fl4Spec.mask
    rw [BitVec.toNat_sub]
    simp only [Nat.one_shiftLeft]
    simp
    omega
  cases sz <;> simp only [frameSizeOf, frameBitsN, Fl4Spec.pageBitsForSize, Fl4Spec.pageBits,
    Fl4Spec.ptTranslationBits] <;> rw [BitVec.toNat_and, h _ (by norm_num), Nat.and_two_pow_sub_one_eq_mod]

set_option maxHeartbeats 2000000 in
/-- **`EpBufHyps.lookup`** from the CSpace relation and `IpcBufCapOK`: FL4's
buffer address is 0 exactly when the spec's TCB has no buffer. -/
theorem lookup_buf_full {th : TypedHeap} (s : S) (σ : Fl4Spec.State Unit) (hR : StateRel th (L.mem s) σ)
    (hV : SlotsValid th (L.mem s)) {t : U64} (ht : th t = some .tcb) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hOK : IpcBufCapOK σ) (b : Bool) :
    msg.lookup_ipc_buffer st s b t ⦃ w => (w = 0#u64 ↔ ipcBufOf b x = none) ∧
      ((L.mem s (tIpcBufA t)).bv = x.tcbIpcBuffer → ∀ p', ipcBufOf b x = some p' → w.bv = p') ⦄ := by
  obtain ⟨x', c, hkx, hc, hca⟩ := hR.bufCap ht
  rw [hk] at hkx; cases hkx
  have hab := hca.2
  unfold msg.lookup_ipc_buffer
  step with obj.Tcb.ipc_buffer.spec' as ⟨wv, hwv⟩
  rw [tcb_slot_buffer]
  apply ok_bind_spec
  rw [slot_cap_eq, hc]
  apply ok_bind_spec
  have hnone : ∀ (hn : ipcBufOf b x = none), (ok 0#u64 : Result U64) ⦃ w => (w = 0#u64 ↔ ipcBufOf b x = none) ∧
      ((L.mem s (tIpcBufA t)).bv = x.tcbIpcBuffer → ∀ p', ipcBufOf b x = some p' → w.bv = p') ⦄ :=
    fun hn => by rw [WP.spec_ok]; exact ⟨⟨fun _ => hn, fun _ => rfl⟩, fun _ p' h => by rw [hn] at h; cases h⟩
  have hother : ∀ (h : ∀ dev p R mt vms md, x.tcbIpcframe ≠ .archObjectCap (.pageCap dev p R mt vms md)),
      (ok 0#u64 : Result U64) ⦃ w => (w = 0#u64 ↔ ipcBufOf b x = none) ∧
      ((L.mem s (tIpcBufA t)).bv = x.tcbIpcBuffer → ∀ p', ipcBufOf b x = some p' → w.bv = p') ⦄ := by
    intro h
    apply hnone
    unfold ipcBufOf
    split
    · rename_i _ p R _ vms md he; exact absurd he (h _ _ _ _ _ _)
    · rfl
  cases c with
  | Frame p sz r dev m ept asid va =>
    simp only [absCap] at hab
    have hwf : 1 ≤ r.val ∧ r.val ≤ 3 := hca.1
    by_cases hdev : dev = true
    · subst hdev
      simp only [↓reduceIte]
      apply hnone
      unfold ipcBufOf
      rw [← hab]
      simp only
      rw [if_neg]
      intro hc'
      have hro : Fl4Spec.vmReadOnly ⊆ vmRightsOf r := by
        rcases hc' with h | ⟨h, -⟩
        · exact fun z hz => h (by unfold Fl4Spec.vmReadOnly Fl4Spec.vmReadWrite at *; simp at hz ⊢; simp [hz])
        · exact h
      have := (hOK t.bv x hk _ _ _ _ _ _ hab.symm hro).1
      cases this
    · have hdev' : dev = false := by simpa using hdev
      subst hdev'
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hal : p.val % 2 ^ frameBitsN sz = 0 := hV.tcb t ht 2 (by decide) _ hc
      classical
      have hsp : ipcBufOf b x = if Fl4Spec.vmReadWrite ⊆ vmRightsOf r ∨ Fl4Spec.vmReadOnly ⊆ vmRightsOf r ∧ ¬ b = true
          then some (p.bv + (x.tcbIpcBuffer &&& Fl4Spec.mask (Fl4Spec.pageBitsForSize (frameSizeOf sz)))) else none := by
        unfold ipcBufOf; rw [← hab]
      have hsome : Fl4Spec.vmReadOnly ⊆ vmRightsOf r → (Fl4Spec.vmReadWrite ⊆ vmRightsOf r ∨
          Fl4Spec.vmReadOnly ⊆ vmRightsOf r ∧ ¬ b = true) → (do
          let bits ← capability.FrameSize.bits sz
          let i ← lift (bits &&& 63#u64)
          let i1 ← 1#u64 <<< i
          let i2 ← lift (core.num.U64.wrapping_sub i1 1#u64)
          let i3 ← lift (wv &&& i2)
          ok (core.num.U64.wrapping_add p i3)) ⦃ w => (w = 0#u64 ↔ ipcBufOf b x = none) ∧
            ((L.mem s (tIpcBufA t)).bv = x.tcbIpcBuffer → ∀ p', ipcBufOf b x = some p' → w.bv = p') ⦄ := by
        intro hro hc'
        have hp0 : p ≠ 0#u64 := by
          have := (hOK t.bv x hk false p.bv _ _ _ _ hab.symm hro).2.1
          intro e; exact this (by rw [e]; rfl)
        refine WP.spec_mono (frame_off_spec sz p wv hal) fun v hv => ?_
        rw [hsp, if_pos hc']
        refine ⟨⟨fun e => ?_, fun e => by cases e⟩, fun hw p' hp' => ?_⟩
        · have : p.val ≠ 0 := fun h => hp0 (UScalar.eq_of_val_eq (by simpa using h))
          rw [e] at hv; simp at hv; omega
        · cases hp'
          have hpv := p.hBounds
          have hwvb : wv.bv = x.tcbIpcBuffer := by rw [hwv]; exact hw
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, frame_mask_toNat, ← hwvb]
          change v.val = (p.val + wv.val % 2 ^ frameBitsN sz) % 2 ^ 64
          rw [hv]
          have hk : 0 < 2 ^ frameBitsN sz := by positivity
          have hb : 2 ^ frameBitsN sz ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by cases sz <;> simp [frameBitsN])
          have := Nat.mod_lt wv.val hk
          simp only [UScalarTy.numBits] at hpv
          have h1 : p.val + 2 ^ frameBitsN sz ≤ 2 ^ 64 := by
            have h2 : 2 ^ frameBitsN sz ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by cases sz <;> simp [frameBitsN])
            have h3 : 2 ^ frameBitsN sz ∣ p.val := Nat.dvd_of_mod_eq_zero hal
            obtain ⟨a, ha⟩ := h3; obtain ⟨b', hb'⟩ := h2
            have : a < b' := by
              by_contra hc; push_neg at hc
              have := Nat.mul_le_mul_left (2 ^ frameBitsN sz) hc
              omega
            have := Nat.mul_le_mul_left (2 ^ frameBitsN sz) (Nat.succ_le_of_lt this)
            rw [Nat.mul_succ] at this; omega
          rw [Nat.mod_eq_of_lt (show p.val + wv.val % 2 ^ frameBitsN sz < 2 ^ 64 by omega)]
      by_cases h3 : r = capability.VM_READ_WRITE
      · rw [if_pos h3]
        have hr3 : r.val = 3 := by rw [h3]; unfold capability.VM_READ_WRITE; rfl
        exact hsome (vmRights_ro.2 (Or.inl hr3)) (Or.inl (vmRights_rw.2 hr3))
      · rw [if_neg h3]
        have hr3 : r.val ≠ 3 := fun h => h3 (UScalar.eq_of_val_eq (by rw [h]; unfold capability.VM_READ_WRITE; rfl))
        cases b with
        | true =>
          simp only [↓reduceIte]
          apply hnone
          rw [hsp, if_neg]
          rintro (h | ⟨-, h⟩)
          · exact hr3 (vmRights_rw.1 h)
          · exact h rfl
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases h2 : r = capability.VM_READ_ONLY
          · rw [if_pos h2]
            have hr2 : r.val = 2 := by rw [h2]; unfold capability.VM_READ_ONLY; rfl
            exact hsome (vmRights_ro.2 (Or.inr hr2)) (Or.inr ⟨vmRights_ro.2 (Or.inr hr2), by simp⟩)
          · rw [if_neg h2]
            have hr2 : r.val ≠ 2 := fun h => h2 (UScalar.eq_of_val_eq (by rw [h]; unfold capability.VM_READ_ONLY; rfl))
            apply hnone
            rw [hsp, if_neg]
            rintro (h | ⟨h, -⟩)
            · exact hr3 (vmRights_rw.1 h)
            · rcases vmRights_ro.1 h with h | h
              · exact hr3 h
              · exact hr2 h
  | _ => exact hother (by intro dev p R mt vms md h; rw [← hab] at h; simp [absCap] at h)

theorem lookup_buf_rel {th : TypedHeap} (s : S) (σ : Fl4Spec.State Unit) (hR : StateRel th (L.mem s) σ)
    (hV : SlotsValid th (L.mem s)) {t : U64} (ht : th t = some .tcb) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hOK : IpcBufCapOK σ) (b : Bool) :
    msg.lookup_ipc_buffer st s b t ⦃ w => (w = 0#u64 ↔ ipcBufOf b x = none) ⦄ :=
  WP.spec_mono (lookup_buf_full s σ hR hV ht hk hOK b) fun _ h => h.1

end Lookup


/-! ## `EpBufHyps` on `SRT … SRE` -/

section Top
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **`EpBufHyps` for `SRT … SRE`**, from `IpcBufCapOK` (named). -/
theorem epBufHyps_top
    (hOK : ∀ s σ, Ipc.SRT st th cr N T C E R B c (Ipc.SRE st N T C E R B c) s σ → IpcBufCapOK σ) :
    EpBufHyps st T E R B (Ipc.SRT st th cr N T C E R B c (Ipc.SRE st N T C E R B c)) :=
  ⟨fun s σ t x b _ hS _ hk => by
    obtain ⟨⟨G, hB⟩, -⟩ := hS.1
    exact lookup_buf_rel s σ hB.2.1.1 hB.2.1.2.1 (Ipc.RelTopB.tcbT hB hk) hk (hOK s σ hS) b⟩

theorem and_not_mask_toNat (x : BitVec 64) (k : Nat) (hk : k ∈ [12, 21, 30]) :
    (x &&& ~~~(Fl4Spec.mask k : BitVec 64)).toNat = x.toNat / 2 ^ k * 2 ^ k := by
  have e : ~~~(Fl4Spec.mask k : BitVec 64) = BitVec.allOnes 64 <<< k := by
    simp at hk; rcases hk with rfl | rfl | rfl <;> decide
  rw [e, ← BitVec.shiftLeft_ushiftRight]
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self _ _) x.isLt)]

theorem pageBits_mem (vms : Fl4Spec.VMPageSize) : Fl4Spec.pageBitsForSize vms ∈ [12, 21, 30] := by
  cases vms <;> simp [Fl4Spec.pageBitsForSize, Fl4Spec.pageBits, Fl4Spec.ptTranslationBits]

theorem mask_toNat' (k : Nat) (hk : k ∈ [12, 21, 30]) (tb : BitVec 64) :
    (tb &&& (Fl4Spec.mask k : BitVec 64)).toNat = tb.toNat % 2 ^ k := by
  have h : (Fl4Spec.mask k : BitVec 64).toNat = 2 ^ k - 1 := by
    simp at hk; rcases hk with rfl | rfl | rfl <;> decide
  rw [BitVec.toNat_and, h, Nat.and_two_pow_sub_one_eq_mod]

/-- **A buffer word's frame**: the base of the page holding word `k < 128`
of an aligned buffer in an aligned page is the page. -/
theorem buf_frame_base (vms : Fl4Spec.VMPageSize) (pb tb : BitVec 64) (k : Nat) (hk : k < 128)
    (hpb : pb.toNat % 2 ^ Fl4Spec.pageBitsForSize vms = 0) (htb : tb.toNat % 1024 = 0) :
    (bufAddr (pb + (tb &&& Fl4Spec.mask (Fl4Spec.pageBitsForSize vms))) k &&&
      ~~~(Fl4Spec.mask (Fl4Spec.pageBitsForSize vms) : BitVec 64)) = pb := by
  have hm := pageBits_mem vms
  set b := Fl4Spec.pageBitsForSize vms with hbdef
  have hb : 12 ≤ b ∧ b ≤ 30 := by simp at hm; omega
  have h2b : 1024 ∣ 2 ^ b := by
    have : 2 ^ 10 ∣ 2 ^ b := Nat.pow_dvd_pow 2 (by omega)
    simpa using this
  have hpos : 0 < 2 ^ b := by positivity
  have hpbL := pb.isLt
  have htbL := tb.isLt
  -- the offset
  have hoff := mask_toNat' b hm tb
  have hoff1 : tb.toNat % 2 ^ b % 1024 = 0 := by
    rw [Nat.mod_mod_of_dvd _ h2b]; exact htb
  have hoff2 : tb.toNat % 2 ^ b < 2 ^ b := Nat.mod_lt _ hpos
  -- the base is at most `2 ^ 64 - 2 ^ b`
  have hb64 : 2 ^ b ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
  have hpbm : pb.toNat + 2 ^ b ≤ 2 ^ 64 := by
    obtain ⟨a, ha⟩ := Nat.dvd_of_mod_eq_zero hpb
    obtain ⟨c, hc⟩ := hb64
    have : a < c := by
      by_contra h; push_neg at h
      have := Nat.mul_le_mul_left (2 ^ b) h; omega
    have := Nat.mul_le_mul_left (2 ^ b) (Nat.succ_le_of_lt this)
    rw [Nat.mul_succ] at this; omega
  apply BitVec.eq_of_toNat_eq
  rw [and_not_mask_toNat _ _ hm]
  unfold bufAddr
  rw [BitVec.toNat_add, BitVec.toNat_add, hoff, BitVec.toNat_ofNat]
  have hk8 : k * Fl4Spec.wordSize % 2 ^ 64 = k * 8 := by
    simp only [Fl4Spec.wordSize]; omega
  rw [hk8]
  have h1 : (pb.toNat + tb.toNat % 2 ^ b) % 2 ^ 64 = pb.toNat + tb.toNat % 2 ^ b := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  have h3 : tb.toNat % 2 ^ b + k * 8 < 2 ^ b := by
    have : tb.toNat % 2 ^ b ≤ 2 ^ b - 1024 := by
      obtain ⟨q, hq⟩ := h2b
      omega
    omega
  rw [Nat.mod_eq_of_lt (by omega)]
  obtain ⟨a, ha⟩ := Nat.dvd_of_mod_eq_zero hpb
  rw [ha, Nat.add_assoc, Nat.mul_add_div hpos, Nat.div_eq_of_lt h3, Nat.add_zero, Nat.mul_comm]

/-- **`EpBufMapHyps` for `SRT … SRE`**, from `IpcBufCapOK` and `BufCover`
(named); `BufWordRel` is `VsP`'s. -/
theorem epBufMapHyps_top (hP0 : Ipc.IPlaced N T E R B)
    (hOK : ∀ s σ, Ipc.SRT st th cr N T C E R B c (Ipc.SRE st N T C E R B c) s σ → IpcBufCapOK σ)
    (hBC : ∀ s σ, Ipc.SRT st th cr N T C E R B c (Ipc.SRE st N T C E R B c) s σ → BufCover T B σ) :
    EpBufMapHyps st T E R B (Ipc.SRT st th cr N T C E R B c (Ipc.SRE st N T C E R B c)) := by
  -- the spec's buffer, unfolded
  have hbuf : ∀ (σ : Fl4Spec.State Unit) (t : U64) (x : Fl4Spec.Tcb) (b : Bool) (p : Fl4Spec.ObjRef),
      IpcBufCapOK σ → σ.kheap t.bv = some (.tcb x) → ipcBufOf b x = some p →
      ∃ pb vms, (∀ k, k < 128 →
          Fl4Spec.inUserFrame (bufAddr (pb + (x.tcbIpcBuffer &&& Fl4Spec.mask (Fl4Spec.pageBitsForSize vms))) k) σ) ∧
        pb ≠ 0 ∧
        pb.toNat % 2 ^ Fl4Spec.pageBitsForSize vms = 0 ∧ x.tcbIpcBuffer.toNat % 1024 = 0 ∧
        p = pb + (x.tcbIpcBuffer &&& Fl4Spec.mask (Fl4Spec.pageBitsForSize vms)) := by
    intro σ t x b p hO hk hp
    unfold ipcBufOf at hp
    split at hp
    · rename_i dev pb R mt vms md he
      split_ifs at hp with hc
      cases hp
      have hro : Fl4Spec.vmReadOnly ⊆ R := by
        rcases hc with h | ⟨h, -⟩
        · exact fun z hz => h (by unfold Fl4Spec.vmReadOnly Fl4Spec.vmReadWrite at *; simp at hz ⊢; simp [hz])
        · exact h
      obtain ⟨-, h0, hd, ha, hpa⟩ := hO t.bv x hk dev pb R mt vms md he hro
      exact ⟨pb, vms, hd, h0, hpa, ha, rfl⟩
    · cases hp
  refine ⟨fun s σ t x b p _ hS ht hk hp => ?_, fun s σ t x p _ hS _ hk hp k hk128 => ?_,
    fun s σ t x p hR hS ht hk hp => ?_⟩
  · obtain ⟨⟨G, hB⟩, -⟩ := hS.1
    refine WP.spec_mono (lookup_buf_full s σ hB.2.1.1 hB.2.1.2.1 (Ipc.RelTopB.tcbT hB hk) hk (hOK s σ hS) b) ?_
    rintro w ⟨h0, hw⟩
    obtain ⟨x', hk', hwx⟩ := hS.1.2.bw t ht
    rw [hk] at hk'; cases hk'
    have hwp := hw hwx p hp
    exact ⟨fun e => (by have h := h0.1 e; rw [hp] at h; cases h), hBC s σ hS t ht x b p hk hp w hwp⟩
  · obtain ⟨pb, vms, hd, -, hpa, ha, rfl⟩ := hbuf σ t x true p (hOK s σ hS) hk hp
    exact hd k hk128
  · obtain ⟨⟨G, hB⟩, -⟩ := hS.1
    obtain ⟨pb, vms, hd, h0, hpa, ha, hpe⟩ := hbuf σ t x true p (hOK s σ hS) hk hp
    have hp0 : (⟨p⟩ : U64) ≠ 0#u64 := by
      intro e
      have e' : p = 0 := congrArg UScalar.bv e
      have hb := pageBits_mem vms
      have := buf_frame_base vms pb x.tcbIpcBuffer 0 (by norm_num) hpa ha
      rw [← hpe] at this
      unfold bufAddr at this
      rw [e'] at this
      simp at this
      exact h0 this.symm
    have hm := hBC s σ hS t ht x true p hk hp ⟨p⟩ rfl
    obtain ⟨dest, slots, heq, -⟩ := WP.spec_exists (Ipc.get_receive_slot_top hP0 hB hR (Ipc.RelTopB.tcbT hB hk) hm hp0 []
      (Aeneas.Std.Array.repeat 3#usize 0#u64))
    exact ⟨slots, heq⟩

end Top

end

end Fl4Proofs.P3.Endp
