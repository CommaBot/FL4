/-
P3x for virtualization (line virt, gen 14, item 1): **the FL4 program walk of `vcpu::init`, whole** (FL4
`crates/fl4-core/src/vcpu.rs` `init` l. 644-678, `reset_svm` l. 679-705; extracted `vcpu.init`, `vcpu.init_loop1`,
`vcpu.reset_svm`, `vcpu.reset_svm_loop`), from a zeroed VCPU object to gen 11's images `InitImgVmx` / `InitImgSvm`
(P3/VirtSanRel), hence to the spec's `initVcpu` (Ext/VirtState, the retype hook of `fl4InvokeUntypedV`).

* `vmcs_addr_eq`: FL4's `vmcs_addr v f` is `vpl v f = v + vmcsOff f` (every encoding); `vpl_fact`, `vplx_inj` (places
  of table fields are distinct, by gen 11's `vmcsOff_inj`).
* **`init_loop1_img`** (`WRITE_FIELDS` loop, 73 × `sanitize_vmcs(f, 0)` + `write_vmcs`): every field's place holds
  `vsan f old` (the spec's `sanitizeVmcs f 0` value by `sanitize_vmcs_rel`, the old word if it refused), every other
  aligned word kept.
* **`init_vmx_img`**: `virtualization() ≠ 2` ⇒ the result is an `InitImgVmx` image (`memW`: the store read as the
  relation's `mem`), incl. the ENTRY (`sanitize_vmcs(ENTRY, 1 << 9)`), RFLAGS and PAT rewrites (`vmx_init_vmcs`).
* `reset_loop_img`, **`reset_svm_img`** (`reset_svm` exactly: save area `[0x400, END)` = `svmSaveU`, `SVM_CPU` 0,
  every other aligned word kept); **`svm_tab`**: FL4's VMCB image (`svmImgU`, the five control words over
  `reset_svm`) is `svmInitFields` at every 8-aligned offset below `END` (`decide +kernel`, 221 cases);
  **`init_svm_img`**: `virtualization() = 2` ⇒ `InitImgSvm`. `initCommon_of`: the shared words.
* **`init_rel_vmx`**, **`init_rel_svm`**, **`init_rel`**: retype → init relates FL4's new VCPU to `initVcpu`
  (on the spec's backend, under `VirtCodeAgree`).

Named premises:
* `CapAgree ar a` [P] (gen 11's, unchanged: `vcpu_capability` = spec `vcpuCapability`).
* **`InitListOut st s v` [J]** (new): the two list words `init` writes besides the object (`ks::VCPU_HEAD`, and when
  the list is not empty the old head's `PREV`) are aligned and lie outside `[v, v + 0x8000)` — mmuAD's `hh` plus the
  disjointness half of its `hd` (the head word is in the kernel-global area; the old head is an older VCPU, apart
  from the freshly retyped object). Not false on reachable states: kernel globals are never untyped memory, and the
  list holds only existing VCPUs, none of which is the fresh object.
* **`VirtCodeAgree ar a` [P]** (new, only in `init_rel`): `virtualization()` is 2 iff `virtKind = .svm` (= mmuAD's
  `ZvVirtAgree`); holds on the existing top's platform (`virtualization() = 0`, `virtKind = .none`).
State hypotheses (not premises): `VFits v` (mmuAD's layout), `VZero st s v` (the retype's clearing: aligned words of
the object zero; mmuAD's `WinZero` gives it). New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtInitIo
import Fl4Proofs.P3.VirtMsrEq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtInitWalk
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel

noncomputable section

theorem shr_1 (x : U64) : x >>> (1#i32) = ok ⟨x.bv >>> 1⟩ := by
  rw [shr_i32 x _ (by decide) (by decide)]; rfl
theorem shr_10 (x : U64) : x >>> (10#i32) = ok ⟨x.bv >>> 10⟩ := by
  rw [shr_i32 x _ (by decide) (by decide)]; rfl
theorem shl_7 (x : U64) : x <<< (7#i32) = ok ⟨x.bv <<< 7⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl

theorem mul8 (x : U64) (h : x.val < 2048) : x * 8#u64 = ok (core.num.U64.wrapping_mul x 8#u64) := by
  apply P1.eq_of_spec_fd
  step as ⟨y, hy⟩
  apply UScalar.eq_of_val_eq
  rw [core.num.U64.wrapping_mul_val_eq, hy]
  have h8 : (8#u64).val = 8 := by first | rfl | simp
  rw [h8]; symm; apply Nat.mod_eq_of_lt
  first | (simp [U64.size]; omega) | (simp [U64.size_def, U64.numBits]; omega) | (simp [U64.size_def]; omega) | scalar_tac

theorem SHADOW_bv : vcpu.SHADOW.bv = VcpuLay.SHADOW := by unfold vcpu.SHADOW; rfl

/-- FL4's place of VMCS field `f` in the VCPU at `v` (`vmcs_addr`). -/
def vpl (v f : U64) : U64 := ⟨v.bv + vmcsOff f.bv⟩

/-- **FL4's `vmcs_addr` is the spec's place** `v + vmcsOff f` (every encoding). -/
theorem vmcs_addr_eq (v f : U64) : vcpu.vmcs_addr v f = ok (vpl v f) := by
  unfold vcpu.vmcs_addr
  simp only [lift, bind_ok, shr_1, shr_10, shr_13, shl_7, shl_9]
  rw [mul8 _ (by exact VirtVcpuRel.vmcsIdx_lt f.bv), bind_ok]
  apply congrArg ok
  apply u64_ext
  unfold vpl
  rw [VirtMsrEq.wadd_bv, VirtMsrEq.wadd_bv, VirtMsrEq.wmul_bv, SHADOW_bv, BitVec.add_assoc]
  rfl

/-- FL4's `WRITE_FIELDS` as a list. -/
def WF : List U64 := vcpu.WRITE_FIELDS.val

theorem WF_len : WF.length = 73 := by
  unfold WF; simp

theorem wf_slice_len : (Slice.len (Array.to_slice vcpu.WRITE_FIELDS)).val = 73 := by
  simp [Slice.len]

theorem wf_writable {f : U64} (h : f ∈ WF) : Vmx.writable f.bv = true := by
  unfold Vmx.writable
  rw [← write_map]
  simp only [decide_eq_true_eq]
  exact List.mem_map_of_mem h


/-- The value `init`'s loop leaves at a field's place: the sanitized zero, or the old word if FL4's sanitizer
refuses (then it writes nothing). -/
def vsan (f d : Word) : Word :=
  match sanitizeVmcs f 0 with
  | .ok x => x
  | .error _ => d

theorem vpl_off (v f : U64) : ∃ o : U64, o.val < 20480 ∧ o.val % 8 = 0 ∧ vpl v f = core.num.U64.wrapping_add v o := by
  have h := P1.vcpu.vmcs_addr.off v f
  rw [vmcs_addr_eq, WP.spec_ok] at h
  exact h

theorem vpl_fact {v : U64} (hv : VFits v) (f : U64) : P1.Aligned (vpl v f) ∧ (vpl v f).val < v.val + 20480 ∧
    v.val ≤ (vpl v f).val := by
  obtain ⟨o, h1, h2, e⟩ := vpl_off v f
  have ha := (vw_of_off hv (o := o) (by omega) h2 (by omega)).2
  have hval := vfits_wadd hv (o := o) (by omega)
  rw [e]; exact ⟨ha, by omega, by omega⟩

theorem vpl_inj {v f g : U64} (hf : f ∈ WF) (hg : g ∈ WF) (e : (vpl v f).val = (vpl v g).val) : f = g := by
  have e1 : vpl v f = vpl v g := UScalar.eq_of_val_eq e
  have e2 : v.bv + vmcsOff f.bv = v.bv + vmcsOff g.bv := congrArg UScalar.bv e1
  exact u64_ext (vmcsOff_inj (Or.inl (wf_writable hf)) (Or.inl (wf_writable hg)) (add_left_cancel e2))

theorem us_lt {a b : Usize} : a < b ↔ a.val < b.val := by simp [UScalar.lt_equiv]

theorem z_bv : U64.bv 0#u64 = (0 : Word) := by first | rfl | decide | simp

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A} {a : A}

theorem take_succ_mem {l : List U64} {j : Nat} (hj : j < l.length) (g : U64) :
    g ∈ l.take (j + 1) ↔ g ∈ l.take j ∨ g = l[j] := by
  rw [List.take_succ, List.getElem?_eq_getElem hj, List.mem_append]
  simp only [Option.toList_some, List.mem_singleton]

/-- **`init`'s `WRITE_FIELDS` loop, exactly** (vcpu.rs l. 664-672): every field's place holds `vsan` of the start's
word there, every other aligned word is the start's. -/
theorem init_loop1_img (hc : CapAgree ar a) {v : U64} (hv : VFits v) (s0 : S) :
    vcpu.init_loop1 st ar s0 a v 0#usize ⦃ s' =>
      (∀ b, P1.Aligned b → (∀ f ∈ WF, (vpl v f).val ≠ b.val) → L.mem s' b = L.mem s0 b) ∧
      ∀ f ∈ WF, (L.mem s' (vpl v f)).bv = vsan f.bv (L.mem s0 (vpl v f)).bv ⦄ := by
  unfold vcpu.init_loop1
  apply loop.spec_decr_nat (measure := fun x : S × Usize => 73 - x.2.val)
    (inv := fun x => x.2.val ≤ 73 ∧
      (∀ b, P1.Aligned b → (∀ f ∈ WF.take x.2.val, (vpl v f).val ≠ b.val) → L.mem x.1 b = L.mem s0 b) ∧
      ∀ f ∈ WF.take x.2.val, (L.mem x.1 (vpl v f)).bv = vsan f.bv (L.mem s0 (vpl v f)).bv)
  · rintro ⟨x0, j⟩ ⟨hj, hfr, hval⟩
    dsimp only at hj hfr hval ⊢
    unfold vcpu.init_loop1.body
    simp only [lift, bind_ok]
    by_cases hlt : j.val < 73
    · have h1 : j < Slice.len (Array.to_slice vcpu.WRITE_FIELDS) :=
        us_lt.2 (by rw [wf_slice_len]; exact hlt)
      simp only [h1, ↓reduceIte]
      have hjl : j.val < WF.length := by rw [WF_len]; exact hlt
      refine WP.spec_bind (Array.index_usize_spec vcpu.WRITE_FIELDS j (by simpa using hlt)) fun f hf => ?_
      have hfe : f = WF[j.val] := by
        first
          | (rw [hf]; exact getElem!_pos WF j.val hjl)
          | (rw [hf]; simp [WF, getElem!_pos, hjl])
          | (simp [WF] at hf ⊢; rw [hf]; simp [getElem!_pos, hjl])
      have htake : ∀ g, g ∈ WF.take (j.val + 1) ↔ g ∈ WF.take j.val ∨ g = f := by
        intro g; rw [take_succ_mem hjl, hfe]
      have hfm : f ∈ WF := by rw [hfe]; exact List.getElem_mem hjl
      obtain ⟨hal, -, -⟩ := vpl_fact hv f
      obtain ⟨r, hr, hrel⟩ := sanitize_vmcs_rel hc f 0#u64
      rw [hr, bind_ok]
      rw [z_bv] at hrel
      cases r with
      | Ok y =>
        have hy : sanitizeVmcs f.bv 0 = .ok y.bv := by
          rcases hs : sanitizeVmcs f.bv 0 with e | x
          · rw [hs] at hrel; exact absurd hrel (by simp [WordResRel])
          · rw [hs] at hrel; simp only [WordResRel] at hrel; rw [hrel]
        simp only
        unfold vcpu.write_vmcs
        rw [vmcs_addr_eq, bind_ok]
        refine WP.spec_bind (P1.LawfulStore.write_spec x0 _ _) fun s2 e => ?_
        subst e
        step as ⟨j1, hj1⟩
        have hj1v : j1.val = j.val + 1 := by scalar_tac
        refine ⟨by omega, fun b hb hn => ?_, fun g hg => ?_, by omega⟩
        · rw [hj1v] at hn
          rw [P1.LawfulStore.mem_wr_val hal hb, if_neg (hn f ((htake f).2 (Or.inr rfl)))]
          exact hfr b hb fun g hg => hn g ((htake g).2 (Or.inl hg))
        · rw [hj1v] at hg
          have hgm : g ∈ WF := List.mem_of_mem_take ((htake g).2 ((htake g).1 hg))
          obtain ⟨halg, -, -⟩ := vpl_fact hv g
          by_cases e : (vpl v f).val = (vpl v g).val
          · have := vpl_inj hfm hgm e
            subst this
            rw [P1.LawfulStore.mem_wr_val hal hal, if_pos rfl]
            unfold vsan; rw [hy]
          · rw [P1.LawfulStore.mem_wr_val hal halg, if_neg e]
            rcases (htake g).1 hg with hg' | rfl
            · exact hval g hg'
            · exact absurd rfl e
      | Err er =>
        have hy : ∃ e, sanitizeVmcs f.bv 0 = .error e := by
          rcases hs : sanitizeVmcs f.bv 0 with e | x
          · exact ⟨e, rfl⟩
          · rw [hs] at hrel; exact absurd hrel (by simp [WordResRel])
        obtain ⟨e0, he0⟩ := hy
        simp only [bind_ok]
        step as ⟨j1, hj1⟩
        have hj1v : j1.val = j.val + 1 := by scalar_tac
        refine ⟨by omega, fun b hb hn => ?_, fun g hg => ?_, by omega⟩
        · rw [hj1v] at hn
          exact hfr b hb fun g hg => hn g ((htake g).2 (Or.inl hg))
        · rw [hj1v] at hg
          rcases (htake g).1 hg with hg' | rfl
          · exact hval g hg'
          · by_cases hin : g ∈ WF.take j.val
            · exact hval g hin
            · have hgm := hfm
              rw [hfr (vpl v g) hal fun h hh e => hin (by
                have := vpl_inj (List.mem_of_mem_take hh) hgm e
                rw [← this]; exact hh)]
              unfold vsan; rw [he0]
    · have h1 : ¬ j < Slice.len (Array.to_slice vcpu.WRITE_FIELDS) := by
        rw [us_lt, wf_slice_len]; exact hlt
      simp only [h1, ↓reduceIte]
      have e : j.val = 73 := by omega
      have ht : WF.take j.val = WF := by rw [e]; exact List.take_of_length_le (by rw [WF_len])
      refine (WP.spec_ok _).2 ⟨fun b hb hn => hfr b hb (by rw [ht]; exact hn), fun f hf => hval f (by rw [ht]; exact hf)⟩
  · refine ⟨by simp, fun b _ _ => rfl, fun f hf => ?_⟩
    simp at hf

end

/-! ## The whole of `vcpu::init` on VMX -/

theorem vo_val {v : U64} (hv : VFits v) {o : Word} (ho : o.toNat < 32768) :
    (⟨v.bv + o⟩ : U64).val = v.val + o.toNat := by
  obtain ⟨h1, h2⟩ := hv
  show (v.bv + o).toNat = _
  rw [BitVec.toNat_add]
  have : v.bv.toNat = v.val := rfl
  rw [this]; exact Nat.mod_eq_of_lt (by omega)

theorem off_toNat (base : Word) (i : Nat) (hb : base.toNat < 32768) (hi : i < 1024) :
    (base + BitVec.ofNat 64 i * 8).toNat = base.toNat + 8 * i := by
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, VirtVcpuRel.toNat_eight]
  rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (a := i * 8) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem vplx_inj {v f g : U64} (hf : Vmx.writable f.bv = true ∨ Vmx.readable f.bv = true)
    (hg : Vmx.writable g.bv = true ∨ Vmx.readable g.bv = true) (e : (vpl v f).val = (vpl v g).val) : f = g := by
  have e1 : vpl v f = vpl v g := UScalar.eq_of_val_eq e
  have e2 : v.bv + vmcsOff f.bv = v.bv + vmcsOff g.bv := congrArg UScalar.bv e1
  exact u64_ext (vmcsOff_inj hf hg (add_left_cancel e2))

theorem mem_WF {f : U64} (h : Vmx.writable f.bv = true) : f ∈ WF := by
  unfold Vmx.writable at h
  rw [← write_map] at h
  simp only [decide_eq_true_eq, List.mem_map] at h
  obtain ⟨g, hg, e⟩ := h
  rwa [← u64_ext e]

theorem CEC_bv : vcpu.vmx.CONTROL_ENTRY_CONTROLS.bv = Vmx.controlEntryControls := by
  unfold vcpu.vmx.CONTROL_ENTRY_CONTROLS; first | rfl | decide
theorem RFL_bv : vcpu.vmx.GUEST_RFLAGS.bv = Vmx.guestRflags := by
  unfold vcpu.vmx.GUEST_RFLAGS; first | rfl | decide
theorem PAT_bv : vcpu.vmx.GUEST_PAT.bv = Vmx.guestPat := by
  unfold vcpu.vmx.GUEST_PAT; first | rfl | decide
theorem CEC_w : Vmx.writable vcpu.vmx.CONTROL_ENTRY_CONTROLS.bv = true := by rw [CEC_bv]; decide
theorem RFL_w : Vmx.writable vcpu.vmx.GUEST_RFLAGS.bv = true := by rw [RFL_bv]; decide
theorem PAT_w : Vmx.writable vcpu.vmx.GUEST_PAT.bv = true := by rw [PAT_bv]; decide

theorem NEXT_val : vcpu.NEXT.val = 20488 := by unfold vcpu.NEXT; rfl
theorem XCR0_val : vcpu.XCR0.val = 20504 := by unfold vcpu.XCR0; rfl

/-- The stored word of a sanitizer verdict, 0 on refusal (`vmxInitFields`' `match … | .error _ => 0`). -/
def resOr (r : Except SyscallError Word) : Word :=
  match r with
  | .ok x => x
  | .error _ => 0

theorem vsan_zero (f : Word) : vsan f 0 = resOr (sanitizeVmcs f 0) := by
  unfold vsan resOr
  rcases sanitizeVmcs f 0 with e | x <;> rfl

theorem vmx_init_vmcs (f : Word) : vmxInitFields (.vmcs f) =
    if f = Vmx.controlEntryControls then resOr (sanitizeVmcs Vmx.controlEntryControls (1 <<< 9))
    else if f = Vmx.guestRflags then 2
    else if f = Vmx.guestPat then 0x0007_0406_0007_0406
    else resOr (sanitizeVmcs f 0) := by
  unfold vmxInitFields resOr
  simp only [reduceCtorEq, if_false, VField.vmcs.injEq]
  rcases sanitizeVmcs Vmx.controlEntryControls (1 <<< 9) with e1 | x1 <;>
    rcases sanitizeVmcs f 0 with e2 | x2 <;> rfl

/-- Outside the VCPU object `[v, v + 0x8000)`. -/
def OutV (v b : U64) : Prop := b.val < v.val ∨ v.val + 32768 ≤ b.val

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A} {a : A}

/-- The VCPU object's aligned words are zero (the retype's clearing; mmuAD's `WinZero` / `JExtVInit`'s `hz`). -/
def VZero (st : machine.Store S) [L : P1.LawfulStore st] (s : S) (v : U64) : Prop :=
  ∀ b, P1.Aligned b → v.val ≤ b.val → b.val < v.val + 32768 → L.mem s b = 0#u64

/-- **`InitListOut` [J]**: the VCPU-list words `init` writes besides the new object — the list head word
(`ks::VCPU_HEAD`) and, when the list is not empty, the old head's `PREV` — are aligned and lie outside the new
VCPU `[v, v + 0x8000)` (mmuAD's `hh` plus the disjointness half of its `hd`: the head word is in the kernel-global
area, the old head is another, older VCPU object, apart from the freshly retyped one). -/
def InitListOut (st : machine.Store S) [L : P1.LawfulStore st] (s : S) (v : U64) : Prop :=
  P1.Aligned (P1.vHeadA st s) ∧ OutV v (P1.vHeadA st s) ∧
  (L.mem s (P1.vHeadA st s) ≠ 0#u64 →
    P1.Aligned (vPrevA (L.mem s (P1.vHeadA st s))) ∧ OutV v (vPrevA (L.mem s (P1.vHeadA st s))))

/-- The memory function the relations read (`VcpuRelVmx`/`VcpuRelSvm`'s `mem`). -/
def memW (st : machine.Store S) [L : P1.LawfulStore st] (s : S) : Word → Word := fun w => (L.mem s ⟨w⟩).bv

set_option maxHeartbeats 4000000 in
/-- **`vcpu::init` on VMX, the whole program** (vcpu.rs l. 644-678, `virtualization() ≠ 2`): from a zeroed VCPU
object, the result is an `InitImgVmx` image. -/
theorem init_vmx_img (hc : CapAgree ar a) {c : U64} (hvirt : ar.virtualization a = ok c) (hc2 : c ≠ 2#u64)
    {v : U64} (hv : VFits v) (s : S) (hz : VZero st s v) (hl : InitListOut st s v) :
    vcpu.init st ar s a v ⦃ s' => InitImgVmx (memW st s') v.bv ⦄ := by
  have hv' := hv
  obtain ⟨hv0, hv1⟩ := hv'
  have hc' : ∀ g, ar.vcpu_capability a g = ok ⟨vcpuCapability g.bv⟩ := hc
  obtain ⟨hha, hho, hhp⟩ := hl
  unfold vcpu.init
  step with P1.obj.ks_get.spec as ⟨hd, ehd⟩
  have ehd' : hd = L.mem s (P1.vHeadA st s) := ehd
  simp only [vcpu.set, lift, bind_ok]
  have aN := (vw_of_off hv (o := vcpu.NEXT) (by rw [NEXT_val]; omega) (by rw [NEXT_val]) (by rw [NEXT_val]; omega)).2
  have vN := vfits_wadd hv (o := vcpu.NEXT) (by rw [NEXT_val]; omega)
  rw [NEXT_val] at vN
  refine WP.spec_bind (P1.LawfulStore.write_spec s _ _) fun s1 e1 => ?_
  subst e1
  -- s2: the old head's PREV word (outside the object)
  refine WP.spec_bind (Pₘ := fun s2 => L.ksb s2 = L.ksb s ∧ ∀ b, P1.Aligned b → v.val ≤ b.val →
      b.val < v.val + 32768 → L.mem s2 b = L.mem (L.wr s (core.num.U64.wrapping_add v vcpu.NEXT) hd) b) ?_
    fun s2 ⟨k2, h2⟩ => ?_
  · split
    · rename_i hn
      have hn' : L.mem s (P1.vHeadA st s) ≠ 0#u64 := by rw [← ehd']; simpa using hn
      obtain ⟨hpa, hpo⟩ := hhp hn'
      refine WP.spec_mono (P1.LawfulStore.write_spec _ _ _) fun s' e => ?_
      subst e
      have ea : core.num.U64.wrapping_add hd vcpu.PREV = vPrevA (L.mem s (P1.vHeadA st s)) := by rw [ehd']; rfl
      rw [ea]
      refine ⟨by simp, fun b hb h1 h2 => ?_⟩
      rw [P1.LawfulStore.mem_wr_ne hpa hb (by unfold OutV at hpo; omega)]
    · exact (WP.spec_ok _).2 ⟨by simp, fun _ _ _ _ => rfl⟩
  step with P1.obj.ks_set.spec as ⟨s3, e3⟩
  subst e3
  have ea : core.num.U64.wrapping_add (L.ksb s2) layout.ks.VCPU_HEAD = P1.vHeadA st s := by
    unfold P1.vHeadA; rw [k2]
  rw [ea, hc', bind_ok]
  have aX := (vw_of_off hv (o := vcpu.XCR0) (by rw [XCR0_val]; omega) (by rw [XCR0_val]) (by rw [XCR0_val]; omega)).2
  have vX := vfits_wadd hv (o := vcpu.XCR0) (by rw [XCR0_val]; omega)
  rw [XCR0_val] at vX
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s4 e4 => ?_
  subst e4
  refine WP.spec_bind (VirtInitIo.init_loop0_io hv _) fun s5 h5 => ?_
  rw [hvirt, bind_ok, if_neg hc2]
  refine WP.spec_bind (init_loop1_img hc hv s5) fun s6 ⟨h6f, h6v⟩ => ?_
  rw [shl_9, bind_ok]
  obtain ⟨re, hre, hrel⟩ := sanitize_vmcs_rel hc vcpu.vmx.CONTROL_ENTRY_CONTROLS ⟨(1#u64).bv <<< 9⟩
  rw [hre, bind_ok]
  simp only [lift, bind_ok, vcpu.write_vmcs, vmcs_addr_eq]
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s7 e7 => ?_
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s8 e8 => ?_
  refine WP.spec_mono (P1.LawfulStore.write_spec _ _ _) fun s9 e9 => ?_
  -- the words below `TCB` (the VMCS image) at s5: zero
  have hlow : ∀ b, P1.Aligned b → v.val ≤ b.val → b.val < v.val + 20480 → L.mem s5 b = 0#u64 := by
    intro b hb hb1 hb2
    have nI : ¬ VirtInitIo.IoR v b 1024 := by unfold VirtInitIo.IoR; omega
    rw [h5 b hb, if_neg nI, P1.LawfulStore.mem_wr_ne aX hb (by omega),
      P1.LawfulStore.mem_wr_ne hha hb (by unfold OutV at hho; omega), h2 b hb hb1 (by omega),
      P1.LawfulStore.mem_wr_ne aN hb (by omega), hz b hb hb1 (by omega)]
  -- the words from `TCB` on at s5
  open Classical in
  have hhigh : ∀ b, P1.Aligned b → v.val + 20480 ≤ b.val → b.val < v.val + 32768 →
      L.mem s5 b = if VirtInitIo.IoR v b 1024 then core.num.U64.MAX
        else if v.val + 20504 = b.val then (⟨vcpuCapability (0#u64).bv⟩ : U64)
        else if v.val + 20488 = b.val then hd else 0#u64 := by
    intro b hb hb1 hb2
    rw [h5 b hb]
    by_cases hI : VirtInitIo.IoR v b 1024
    · rw [if_pos hI, if_pos hI]
    · rw [if_neg hI, if_neg hI, P1.LawfulStore.mem_wr_val aX hb, vX]
      by_cases hX : v.val + 20504 = b.val
      · rw [if_pos hX, if_pos hX]
      · rw [if_neg hX, if_neg hX, P1.LawfulStore.mem_wr_ne hha hb (by unfold OutV at hho; omega),
          h2 b hb (by omega) (by omega), P1.LawfulStore.mem_wr_val aN hb, vN]
        by_cases hN : v.val + 20488 = b.val
        · rw [if_pos hN, if_pos hN]
        · rw [if_neg hN, if_neg hN]; exact hz b hb (by omega) hb2
  obtain ⟨aE, lE, -⟩ := vpl_fact hv vcpu.vmx.CONTROL_ENTRY_CONTROLS
  obtain ⟨aR, lR, -⟩ := vpl_fact hv vcpu.vmx.GUEST_RFLAGS
  obtain ⟨aP, lP, -⟩ := vpl_fact hv vcpu.vmx.GUEST_PAT
  -- the final image from `TCB` on
  have hhi : ∀ b, P1.Aligned b → v.val + 20480 ≤ b.val → L.mem s9 b = L.mem s5 b := by
    intro b hb hb1
    rw [e9, P1.LawfulStore.mem_wr_ne aP hb (by omega), e8, P1.LawfulStore.mem_wr_ne aR hb (by omega),
      e7, P1.LawfulStore.mem_wr_ne aE hb (by omega)]
    exact h6f b hb fun f _ => by have := (vpl_fact hv f).2.1; omega
  have hrel' : WordResRel re (sanitizeVmcs Vmx.controlEntryControls (1 <<< 9)) := by rw [← CEC_bv]; exact hrel
  have pc : Vmx.guestPat ≠ Vmx.controlEntryControls := by decide
  have pr : Vmx.guestPat ≠ Vmx.guestRflags := by decide
  have rc : Vmx.guestRflags ≠ Vmx.controlEntryControls := by decide
  -- the final VMCS image
  have hvm : ∀ F : U64, (Vmx.writable F.bv = true ∨ Vmx.readable F.bv = true) →
      (L.mem s9 (vpl v F)).bv = vmxInitFields (.vmcs F.bv) := by
    intro F hF
    obtain ⟨aF, lF, gF⟩ := vpl_fact hv F
    have h0 : L.mem s5 (vpl v F) = 0#u64 := hlow _ aF gF lF
    have hs6 : (L.mem s6 (vpl v F)).bv = resOr (sanitizeVmcs F.bv 0) := by
      by_cases hw : Vmx.writable F.bv = true
      · rw [h6v F (mem_WF hw), h0, z_bv, vsan_zero]
      · rw [h6f _ aF fun g hg e => hw (by rw [← vplx_inj (Or.inl (wf_writable hg)) hF e]; exact wf_writable hg), h0]
        rcases hsv : sanitizeVmcs F.bv 0 with e | x
        · rfl
        · simp only [Bool.not_eq_true] at hw
          simp [sanitizeVmcs, hw] at hsv
    rw [vmx_init_vmcs, e9, P1.LawfulStore.mem_wr_val aP aF]
    by_cases eP : F = vcpu.vmx.GUEST_PAT
    · subst eP
      rw [if_pos rfl, PAT_bv, if_neg pc, if_neg pr, if_pos rfl]
      first | rfl | decide
    rw [if_neg (fun e => eP (vplx_inj (Or.inl PAT_w) hF e).symm), e8, P1.LawfulStore.mem_wr_val aR aF]
    by_cases eR : F = vcpu.vmx.GUEST_RFLAGS
    · subst eR
      rw [if_pos rfl, RFL_bv, if_neg rc, if_pos rfl]
      first | rfl | decide
    rw [if_neg (fun e => eR (vplx_inj (Or.inl RFL_w) hF e).symm), e7, P1.LawfulStore.mem_wr_val aE aF]
    by_cases eE : F = vcpu.vmx.CONTROL_ENTRY_CONTROLS
    · subst eE
      rw [if_pos rfl, CEC_bv, if_pos rfl]
      cases re with
      | Ok x =>
        rcases hs : sanitizeVmcs Vmx.controlEntryControls (1 <<< 9) with er | y
        · rw [hs] at hrel'; exact absurd hrel' (by simp [WordResRel])
        · rw [hs] at hrel'; simp only [WordResRel] at hrel'
          show x.bv = y
          exact hrel'
      | Err er =>
        rcases hs : sanitizeVmcs Vmx.controlEntryControls (1 <<< 9) with er' | y
        · rfl
        · rw [hs] at hrel'; exact absurd hrel' (by simp [WordResRel])
    rw [if_neg (fun e => eE (vplx_inj (Or.inl CEC_w) hF e).symm), hs6]
    have nP : F.bv ≠ Vmx.guestPat := fun e => eP (u64_ext (by rw [e, PAT_bv]))
    have nR : F.bv ≠ Vmx.guestRflags := fun e => eR (u64_ext (by rw [e, RFL_bv]))
    have nE : F.bv ≠ Vmx.controlEntryControls := fun e => eE (u64_ext (by rw [e, CEC_bv]))
    rw [if_neg nE, if_neg nR, if_neg nP]
  -- zero words above `TCB`
  have hz0 : ∀ o : Word, o.toNat % 8 = 0 → 20480 ≤ o.toNat → o.toNat < 24576 → o.toNat ≠ 20504 →
      o.toNat ≠ 20488 → memW st s9 (v.bv + o) = 0 := by
    intro o h1 h2 h3 h4 h5'
    have e := vo_val hv (o := o) (by omega)
    have hb : P1.Aligned (⟨v.bv + o⟩ : U64) := by unfold P1.Aligned; rw [e]; omega
    have nI : ¬ VirtInitIo.IoR v ⟨v.bv + o⟩ 1024 := by unfold VirtInitIo.IoR; rw [e]; omega
    have n1 : ¬ (v.val + 20504 = (⟨v.bv + o⟩ : U64).val) := by rw [e]; omega
    have n2 : ¬ (v.val + 20488 = (⟨v.bv + o⟩ : U64).val) := by rw [e]; omega
    unfold memW
    rw [hhi _ hb (by rw [e]; omega), hhigh _ hb (by rw [e]; omega) (by rw [e]; omega), if_neg nI, if_neg n1, if_neg n2]
    rfl
  exact
    { tcb := hz0 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      valid := hz0 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      pending := hz0 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      ibpb := hz0 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      cr2 := hz0 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      mrs := fun i => by
        have e := off_toNat VcpuLay.EXIT i.val (by decide) (by omega)
        have hE : VcpuLay.EXIT.toNat = 20992 := by decide
        exact hz0 _ (by unfold exitOff; omega) (by unfold exitOff; omega) (by unfold exitOff; have := i.isLt; omega)
          (by unfold exitOff; omega) (by unfold exitOff; omega)
      gpr := fun i => by
        have e := off_toNat VcpuLay.REGS i.val (by decide) (by omega)
        have hE : VcpuLay.REGS.toNat = 20736 := by decide
        exact hz0 _ (by unfold gprOff; omega) (by unfold gprOff; omega) (by unfold gprOff; have := i.isLt; omega)
          (by unfold gprOff; omega) (by unfold gprOff; omega)
      msr := fun m i hi => by
        unfold msrSlot at hi
        split_ifs at hi <;> (cases hi) <;>
          exact hz0 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      xcr0 := by
        have e := vo_val hv (o := VcpuLay.XCR0) (by decide)
        have hX : VcpuLay.XCR0.toNat = 20504 := by decide
        have hb : P1.Aligned (⟨v.bv + VcpuLay.XCR0⟩ : U64) := by unfold P1.Aligned; rw [e]; omega
        have nI : ¬ VirtInitIo.IoR v ⟨v.bv + VcpuLay.XCR0⟩ 1024 := by unfold VirtInitIo.IoR; rw [e]; omega
        have n1 : v.val + 20504 = (⟨v.bv + VcpuLay.XCR0⟩ : U64).val := by rw [e]; omega
        unfold memW
        rw [hhi _ hb (by rw [e]; omega), hhigh _ hb (by rw [e]; omega) (by rw [e]; omega), if_neg nI, if_pos n1]
        show vcpuCapability (0#u64).bv = vcpuCapability 0
        rfl
      io := fun p => by
        have hp : p.toNat < 65536 := p.isLt
        have hval : (⟨v.bv + vcpuIoOff p⟩ : U64).val = v.val + 24576 + 8 * (p.toNat / 64) := by
          show (v.bv + vcpuIoOff p).toNat = _
          unfold vcpuIoOff
          have e := off_toNat VcpuLay.IO (p.toNat / 64) (by decide) (by omega)
          have hI : VcpuLay.IO.toNat = 24576 := by decide
          rw [BitVec.toNat_add, e, hI]
          have hvb : v.bv.toNat = v.val := rfl
          rw [hvb, Nat.mod_eq_of_lt (by omega)]
          omega
        have hb : P1.Aligned (⟨v.bv + vcpuIoOff p⟩ : U64) := by unfold P1.Aligned; rw [hval]; omega
        have yI : VirtInitIo.IoR v ⟨v.bv + vcpuIoOff p⟩ 1024 := by unfold VirtInitIo.IoR; rw [hval]; omega
        unfold memW
        rw [hhi _ hb (by rw [hval]; omega), hhigh _ hb (by rw [hval]; omega) (by rw [hval]; omega), if_pos yI]
        exact MAX_bv
      vmcs := fun f hf => hvm ⟨f⟩ hf }

end

/-! ## SVM: `reset_svm` and the control words -/

theorem END_eq : vcpu.svm.END = ok 1768#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.svm.END.spec
theorem EFER_eq : vcpu.svm.EFER = ok 1232#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.svm.EFER.spec
theorem SCR0_eq : vcpu.svm.CR0 = ok 1368#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.svm.CR0.spec
theorem DR6_eq : vcpu.svm.DR6 = ok 1384#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.svm.DR6.spec
theorem DR7_eq : vcpu.svm.DR7 = ok 1376#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.svm.DR7.spec
theorem SRFL_eq : vcpu.svm.RFLAGS = ok 1392#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.svm.RFLAGS.spec
theorem SRIP_eq : vcpu.svm.RIP = ok 1400#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.svm.RIP.spec
theorem GPAT_eq : vcpu.svm.G_PAT = ok 1640#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.svm.G_PAT.spec
theorem SVMCPU_val : vcpu.SVM_CPU.val = 20536 := by unfold vcpu.SVM_CPU; rfl
theorem INTCTL_val : vcpu.svm.INT_CTL.val = 96 := by unfold vcpu.svm.INT_CTL; rfl
theorem NESTED_val : vcpu.svm.NESTED_CTL.val = 144 := by unfold vcpu.svm.NESTED_CTL; rfl

/-- `reset_svm`'s segment-attribute byte at save-area offset `o` (vcpu.rs l. 684-692). -/
def attrU (o : Nat) : U64 := if o = 1040 then 155#u64 else if o = 1136 then 130#u64 else if o = 1168 then 139#u64
  else 147#u64

/-- The segment-attribute word `reset_svm`'s loop writes at offset `o`. -/
def segU (o : Nat) : U64 := 281470681743360#u64 ||| (⟨(attrU o).bv <<< 16⟩ : U64)

/-- The save-area word `reset_svm` leaves at offset `o` (`0x400 ≤ o < END`): the last write wins. -/
def svmSaveU (o : Nat) : U64 :=
  if 1640 = o then 1974748653749254#u64 else if 1400 = o then 65520#u64 else if 1392 = o then 2#u64
  else if 1376 = o then 1024#u64 else if 1384 = o then 4294905840#u64 else if 1368 = o then 16#u64
  else if 1232 = o then ⟨(1#u64).bv <<< 12⟩ else if 1048 = o then 4294901760#u64
  else if 1040 = o then 281470691962880#u64
  else if 1024 ≤ o ∧ o < 1184 ∧ o % 16 = 0 then segU o else 0#u64

/-- The VMCB word `init` leaves at offset `o < END` on SVM (the five control words over `reset_svm`). -/
def svmImgU (o : Nat) : U64 :=
  if 144 = o then 1#u64 else if 96 = o then ⟨(1#u64).bv <<< 24⟩ else if 16 = o then vcpu.SVM_I2_FORCED
  else if 8 = o then 393218#u64 ||| (⟨vcpu.SVM_I1_FORCED.bv <<< 32⟩ : U64)
  else if 0 = o then 18446744069415632896#u64
  else if 1024 ≤ o then svmSaveU o else 0#u64

/-- **FL4's SVM image is the spec's `svmInitFields`, word by word** (every 8-aligned VMCB offset below `END`;
FL4 `reset_svm` + `init`'s five control words against `svmReset` / `svmInitFields`, `Ext/VirtState`). -/
theorem svm_tab : ∀ k, k < 221 → (svmImgU (8 * k)).bv = svmInitFields (.vmcb (BitVec.ofNat 64 (8 * k))) := by
  decide +kernel

/-- FL4's word at offset `o` of the VCPU at `v`. -/
def vo (v : U64) (o : Nat) : U64 := ⟨v.bv + BitVec.ofNat 64 o⟩

theorem voN {v : U64} (hv : VFits v) {o : Nat} (ho : o < 32768) : (vo v o).val = v.val + o := by
  obtain ⟨h1, h2⟩ := hv
  show (v.bv + BitVec.ofNat 64 o).toNat = _
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega)]
  have : v.bv.toNat = v.val := rfl
  rw [this]; exact Nat.mod_eq_of_lt (by omega)

theorem attr_eq (off : U64) :
    (if off = 1040#u64 then ok 155#u64 else if off = 1136#u64 then ok 130#u64 else if off = 1168#u64 then ok 139#u64
      else ok 147#u64 : Result U64) = ok (attrU off.val) := by
  have k : ∀ n : U64, (off = n) ↔ off.val = n.val := fun n => ⟨fun h => h ▸ rfl, UScalar.eq_of_val_eq⟩
  have a1 : (1040#u64).val = 1040 := by first | rfl | simp
  have a2 : (1136#u64).val = 1136 := by first | rfl | simp
  have a3 : (1168#u64).val = 1168 := by first | rfl | simp
  simp only [k, a1, a2, a3]
  unfold attrU
  split_ifs <;> rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A} {a : A}

theorem mem_wr_off {v : U64} (hv : VFits v) {c : U64} {n : Nat} (hcv : c.val = n) (hn : n < 32768) (hn8 : n % 8 = 0)
    {o : Nat} (ho : o < 32768) (ho8 : o % 8 = 0) (s : S) (x : U64) :
    L.mem (L.wr s (core.num.U64.wrapping_add v c) x) (vo v o) = if n = o then x else L.mem s (vo v o) := by
  have hv' := hv
  obtain ⟨h1, h2⟩ := hv'
  have ha : P1.Aligned (core.num.U64.wrapping_add v c) := by
    unfold P1.Aligned; rw [vfits_wadd hv (by omega)]; omega
  have hb : P1.Aligned (vo v o) := by unfold P1.Aligned; rw [voN hv ho]; omega
  rw [P1.LawfulStore.mem_wr_val ha hb, vfits_wadd hv (by omega), voN hv ho, hcv]
  by_cases e : n = o
  · rw [if_pos (by omega), if_pos e]
  · rw [if_neg (by omega), if_neg e]

theorem wlit {v : U64} (hv : VFits v) (c : U64) (n : Nat) (hcv : c.val = n) (hn : n < 32768) (hn8 : n % 8 = 0) :
    P1.Aligned (core.num.U64.wrapping_add v c) ∧ (core.num.U64.wrapping_add v c).val = v.val + n := by
  have h := vfits_wadd hv (o := c) (by omega)
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, by rw [h, hcv]⟩
  unfold P1.Aligned; rw [h]; omega

/-- **`reset_svm`'s segment-attribute loop, exactly** (vcpu.rs l. 683-695). -/
theorem reset_loop_img {v : U64} (hv : VFits v) (s0 : S) :
    vcpu.reset_svm_loop st s0 v 1024#u64 ⦃ s' => ∀ b, P1.Aligned b →
      L.mem s' b = if v.val + 1024 ≤ b.val ∧ b.val < v.val + 1184 ∧ (b.val - v.val) % 16 = 0
        then segU (b.val - v.val) else L.mem s0 b ⦄ := by
  have hv' := hv
  obtain ⟨hv0, hv1⟩ := hv'
  unfold vcpu.reset_svm_loop
  apply loop.spec_decr_nat (measure := fun x : S × U64 => 1185 - x.2.val)
    (inv := fun x => x.2.val % 16 = 0 ∧ 1024 ≤ x.2.val ∧ x.2.val ≤ 1184 ∧ ∀ b, P1.Aligned b →
      L.mem x.1 b = if v.val + 1024 ≤ b.val ∧ b.val < v.val + x.2.val ∧ (b.val - v.val) % 16 = 0
        then segU (b.val - v.val) else L.mem s0 b)
  · rintro ⟨x0, x1⟩ ⟨h16, hlo, hhi, hx⟩
    dsimp only at h16 hlo hhi hx ⊢
    unfold vcpu.reset_svm_loop.body
    split
    · rename_i hle
      have hle' : x1.val ≤ 1168 := by simpa using hle
      rw [attr_eq, bind_ok, shl_16, bind_ok]
      simp only [lift, bind_ok, vcpu.set]
      have ha := (vw_of_off hv (o := x1) (by omega) (by omega) (by omega)).2
      have hav := vfits_wadd hv (o := x1) (by omega)
      refine WP.spec_bind (P1.LawfulStore.write_spec x0 _ _) fun s1 e => ?_
      subst e
      step as ⟨off1, hoff1⟩
      have ho1 : off1.val = x1.val + 16 := by scalar_tac
      refine ⟨by omega, by omega, by omega, fun b hb => ?_, by omega⟩
      rw [P1.LawfulStore.mem_wr_val ha hb, hx b hb, hav, ho1]
      by_cases e : v.val + x1.val = b.val
      · have cn : v.val + 1024 ≤ b.val ∧ b.val < v.val + (x1.val + 16) ∧ (b.val - v.val) % 16 = 0 := by omega
        rw [if_pos e, if_pos cn, show b.val - v.val = x1.val by omega]
        all_goals rfl
      · rw [if_neg e]
        have hiff : (v.val + 1024 ≤ b.val ∧ b.val < v.val + x1.val ∧ (b.val - v.val) % 16 = 0) ↔
            (v.val + 1024 ≤ b.val ∧ b.val < v.val + (x1.val + 16) ∧ (b.val - v.val) % 16 = 0) := by omega
        simp only [hiff]
    · rename_i hgt
      have hgt' : ¬ x1.val ≤ 1168 := by simpa using hgt
      have e : x1.val = 1184 := by omega
      refine (WP.spec_ok _).2 fun b hb => ?_
      rw [hx b hb, e]
  · refine ⟨by first | rfl | decide | simp, by first | decide | simp, by first | decide | simp, fun b hb => ?_⟩
    have e : (1024#u64).val = 1024 := by first | rfl | simp
    have n : ¬ (v.val + 1024 ≤ b.val ∧ b.val < v.val + (1024#u64).val ∧ (b.val - v.val) % 16 = 0) := by
      rw [e]; omega
    rw [if_neg n]

set_option maxHeartbeats 4000000 in
/-- **`reset_svm`, exactly** (vcpu.rs l. 679-705): the save-area words `[0x400, END)` hold `svmSaveU`, `SVM_CPU`
is 0, every other aligned word is the start's. -/
theorem reset_svm_img {v : U64} (hv : VFits v) (s0 : S) :
    vcpu.reset_svm st s0 v ⦃ s' =>
      (∀ b, P1.Aligned b → (b.val < v.val + 1024 ∨ v.val + 1768 ≤ b.val) → b.val ≠ v.val + 20536 →
        L.mem s' b = L.mem s0 b) ∧
      (∀ b, P1.Aligned b → b.val = v.val + 20536 → L.mem s' b = 0#u64) ∧
      ∀ o, o % 8 = 0 → 1024 ≤ o → o < 1768 → L.mem s' (vo v o) = svmSaveU o ⦄ := by
  have hv' := hv
  obtain ⟨hv0, hv1⟩ := hv'
  unfold vcpu.reset_svm
  simp only [vcpu.set, lift, bind_ok, END_eq, EFER_eq, SCR0_eq, DR6_eq, DR7_eq, SRFL_eq, SRIP_eq, GPAT_eq, shl_12]
  have aC := (vw_of_off hv (o := vcpu.SVM_CPU) (by rw [SVMCPU_val]; omega) (by rw [SVMCPU_val]) (by rw [SVMCPU_val]; omega)).2
  have vC := vfits_wadd hv (o := vcpu.SVM_CPU) (by rw [SVMCPU_val]; omega)
  rw [SVMCPU_val] at vC
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s1 e1 => ?_
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = 744 := by scalar_tac
  have hp : (core.num.U64.wrapping_add v 1024#u64).val = v.val + 1024 := vfits_wadd hv (by simp)
  have ap : P1.Aligned (core.num.U64.wrapping_add v 1024#u64) := by unfold P1.Aligned; rw [hp]; omega
  refine WP.spec_bind (P1.LawfulStore.zero_spec s1 _ _) fun s2 e2 => ?_
  refine WP.spec_bind (reset_loop_img hv s2) fun s3 h3 => ?_
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s4 e4 => ?_
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s5 e5 => ?_
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s6 e6 => ?_
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s7 e7 => ?_
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s8 e8 => ?_
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s9 e9 => ?_
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s10 e10 => ?_
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s11 e11 => ?_
  refine WP.spec_mono (P1.LawfulStore.write_spec _ _ _) fun s12 e12 => ?_
  obtain ⟨a4, v4⟩ := wlit hv 1040#u64 1040 (by first | rfl | simp) (by norm_num) (by norm_num)
  obtain ⟨a5, v5⟩ := wlit hv 1048#u64 1048 (by first | rfl | simp) (by norm_num) (by norm_num)
  obtain ⟨a6, v6⟩ := wlit hv 1232#u64 1232 (by first | rfl | simp) (by norm_num) (by norm_num)
  obtain ⟨a7, v7⟩ := wlit hv 1368#u64 1368 (by first | rfl | simp) (by norm_num) (by norm_num)
  obtain ⟨a8, v8⟩ := wlit hv 1384#u64 1384 (by first | rfl | simp) (by norm_num) (by norm_num)
  obtain ⟨a9, v9⟩ := wlit hv 1376#u64 1376 (by first | rfl | simp) (by norm_num) (by norm_num)
  obtain ⟨a10, v10⟩ := wlit hv 1392#u64 1392 (by first | rfl | simp) (by norm_num) (by norm_num)
  obtain ⟨a11, v11⟩ := wlit hv 1400#u64 1400 (by first | rfl | simp) (by norm_num) (by norm_num)
  obtain ⟨a12, v12⟩ := wlit hv 1640#u64 1640 (by first | rfl | simp) (by norm_num) (by norm_num)
  -- the zeroing
  have h2 : ∀ b, P1.Aligned b → L.mem s2 b =
      if v.val + 1024 ≤ b.val ∧ b.val < v.val + 1768 then 0#u64 else L.mem s1 b := by
    intro b hb
    rw [e2, L.mem_zr _ _ _ _ ap (by omega) (by rw [hp]; omega) hb, hp, hi2v]
  -- below the save area's writes: s12 = s3 off the nine words
  have hw : ∀ b, P1.Aligned b → (b.val < v.val + 1024 ∨ v.val + 1768 ≤ b.val) → L.mem s12 b = L.mem s3 b := by
    intro b hb hr
    rw [e12, P1.LawfulStore.mem_wr_ne a12 hb (by omega), e11, P1.LawfulStore.mem_wr_ne a11 hb (by omega),
      e10, P1.LawfulStore.mem_wr_ne a10 hb (by omega), e9, P1.LawfulStore.mem_wr_ne a9 hb (by omega),
      e8, P1.LawfulStore.mem_wr_ne a8 hb (by omega), e7, P1.LawfulStore.mem_wr_ne a7 hb (by omega),
      e6, P1.LawfulStore.mem_wr_ne a6 hb (by omega), e5, P1.LawfulStore.mem_wr_ne a5 hb (by omega),
      e4, P1.LawfulStore.mem_wr_ne a4 hb (by omega)]
  refine ⟨fun b hb hr hc => ?_, fun b hb hc => ?_, fun o ho8 ho1 ho2 => ?_⟩
  · have n3 : ¬ (v.val + 1024 ≤ b.val ∧ b.val < v.val + 1184 ∧ (b.val - v.val) % 16 = 0) := by omega
    have n2 : ¬ (v.val + 1024 ≤ b.val ∧ b.val < v.val + 1768) := by omega
    rw [hw b hb hr, h3 b hb, if_neg n3, h2 b hb, if_neg n2, e1, P1.LawfulStore.mem_wr_ne aC hb (by omega)]
  · have hr : v.val + 1768 ≤ b.val := by omega
    have n3 : ¬ (v.val + 1024 ≤ b.val ∧ b.val < v.val + 1184 ∧ (b.val - v.val) % 16 = 0) := by omega
    have n2 : ¬ (v.val + 1024 ≤ b.val ∧ b.val < v.val + 1768) := by omega
    have y1 : (core.num.U64.wrapping_add v vcpu.SVM_CPU).val = b.val := by omega
    rw [hw b hb (Or.inr hr), h3 b hb, if_neg n3, h2 b hb, if_neg n2, e1, P1.LawfulStore.mem_wr_val aC hb, if_pos y1]
  · have vb := voN hv (o := o) (by omega)
    have hb : P1.Aligned (vo v o) := by unfold P1.Aligned; rw [vb]; omega
    have hin : L.mem s3 (vo v o) = if 1024 ≤ o ∧ o < 1184 ∧ o % 16 = 0 then segU o else 0#u64 := by
      rw [h3 _ hb, vb]
      by_cases c : 1024 ≤ o ∧ o < 1184 ∧ o % 16 = 0
      · have c' : v.val + 1024 ≤ v.val + o ∧ v.val + o < v.val + 1184 ∧ (v.val + o - v.val) % 16 = 0 := by omega
        rw [if_pos c', if_pos c, Nat.add_sub_cancel_left]
      · have c' : ¬ (v.val + 1024 ≤ v.val + o ∧ v.val + o < v.val + 1184 ∧ (v.val + o - v.val) % 16 = 0) := by
          omega
        have z : v.val + 1024 ≤ (vo v o).val ∧ (vo v o).val < v.val + 1768 := by rw [vb]; omega
        rw [if_neg c', if_neg c, h2 _ hb, if_pos z]
    rw [e12, P1.LawfulStore.mem_wr_val a12 hb, e11, P1.LawfulStore.mem_wr_val a11 hb,
      e10, P1.LawfulStore.mem_wr_val a10 hb, e9, P1.LawfulStore.mem_wr_val a9 hb,
      e8, P1.LawfulStore.mem_wr_val a8 hb, e7, P1.LawfulStore.mem_wr_val a7 hb,
      e6, P1.LawfulStore.mem_wr_val a6 hb, e5, P1.LawfulStore.mem_wr_val a5 hb,
      e4, P1.LawfulStore.mem_wr_val a4 hb, hin]
    simp only [v4, v5, v6, v7, v8, v9, v10, v11, v12, vb, Nat.add_left_cancel_iff]
    rfl

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- `InitCommon` from FL4's words from `TCB` on: the I/O bitmap all ones, XCR0 the host's, the list's `NEXT` the old
head, every other word zero. -/
theorem initCommon_of {v : U64} (hv : VFits v) {s' : S} {hd : U64}
    (H : ∀ b, P1.Aligned b → v.val + 20480 ≤ b.val → b.val < v.val + 32768 →
      L.mem s' b = (open Classical in if VirtInitIo.IoR v b 1024 then core.num.U64.MAX
        else if v.val + 20504 = b.val then (⟨vcpuCapability (0#u64).bv⟩ : U64)
        else if v.val + 20488 = b.val then hd else 0#u64)) :
    InitCommon (memW st s') v.bv := by
  have hv' := hv
  obtain ⟨hv0, hv1⟩ := hv'
  -- zero words above `TCB`
  have hz0 : ∀ o : Word, o.toNat % 8 = 0 → 20480 ≤ o.toNat → o.toNat < 24576 → o.toNat ≠ 20504 →
      o.toNat ≠ 20488 → memW st s' (v.bv + o) = 0 := by
    intro o h1 h2 h3 h4 h5'
    have e := vo_val hv (o := o) (by omega)
    have hb : P1.Aligned (⟨v.bv + o⟩ : U64) := by unfold P1.Aligned; rw [e]; omega
    have nI : ¬ VirtInitIo.IoR v ⟨v.bv + o⟩ 1024 := by unfold VirtInitIo.IoR; rw [e]; omega
    have n1 : ¬ (v.val + 20504 = (⟨v.bv + o⟩ : U64).val) := by rw [e]; omega
    have n2 : ¬ (v.val + 20488 = (⟨v.bv + o⟩ : U64).val) := by rw [e]; omega
    unfold memW
    rw [H _ hb (by rw [e]; omega) (by rw [e]; omega), if_neg nI, if_neg n1, if_neg n2]
    rfl
  exact
    { tcb := hz0 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      valid := hz0 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      pending := hz0 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      ibpb := hz0 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      mrs := fun i => by
        have e := off_toNat VcpuLay.EXIT i.val (by decide) (by omega)
        have hE : VcpuLay.EXIT.toNat = 20992 := by decide
        exact hz0 _ (by unfold exitOff; omega) (by unfold exitOff; omega) (by unfold exitOff; have := i.isLt; omega)
          (by unfold exitOff; omega) (by unfold exitOff; omega)
      gpr := fun i => by
        have e := off_toNat VcpuLay.REGS i.val (by decide) (by omega)
        have hE : VcpuLay.REGS.toNat = 20736 := by decide
        exact hz0 _ (by unfold gprOff; omega) (by unfold gprOff; omega) (by unfold gprOff; have := i.isLt; omega)
          (by unfold gprOff; omega) (by unfold gprOff; omega)
      xcr0 := by
        have e := vo_val hv (o := VcpuLay.XCR0) (by decide)
        have hX : VcpuLay.XCR0.toNat = 20504 := by decide
        have hb : P1.Aligned (⟨v.bv + VcpuLay.XCR0⟩ : U64) := by unfold P1.Aligned; rw [e]; omega
        have nI : ¬ VirtInitIo.IoR v ⟨v.bv + VcpuLay.XCR0⟩ 1024 := by unfold VirtInitIo.IoR; rw [e]; omega
        have n1 : v.val + 20504 = (⟨v.bv + VcpuLay.XCR0⟩ : U64).val := by rw [e]; omega
        unfold memW
        rw [H _ hb (by rw [e]; omega) (by rw [e]; omega), if_neg nI, if_pos n1]
        show vcpuCapability (0#u64).bv = vcpuCapability 0
        rfl }

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A} {a : A}

theorem readable_nat {off : Word} (h : Svm.readable off = true) : off.toNat % 8 = 0 ∧ off.toNat < 1768 := by
  simp only [Svm.readable, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have e1 := congrArg BitVec.toNat h1
  rw [BitVec.toNat_and] at e1
  have h7 : (7 : Word).toNat = 2 ^ 3 - 1 := rfl
  rw [h7, Nat.and_two_pow_sub_one_eq_mod] at e1
  rw [BitVec.lt_def] at h2
  have hE : Svm.svmEnd.toNat = 1768 := by decide
  exact ⟨by simpa using e1, by omega⟩

set_option maxHeartbeats 4000000 in
/-- **`vcpu::init` on SVM, the whole program** (vcpu.rs l. 644-662 and `reset_svm` l. 679-705,
`virtualization() = 2`): from a zeroed VCPU object, the result is an `InitImgSvm` image. -/
theorem init_svm_img (hc : CapAgree ar a) {c : U64} (hvirt : ar.virtualization a = ok c) (hc2 : c = 2#u64)
    {v : U64} (hv : VFits v) (s : S) (hz : VZero st s v) (hl : InitListOut st s v) :
    vcpu.init st ar s a v ⦃ s' => InitImgSvm (memW st s') v.bv ⦄ := by
  have hv' := hv
  obtain ⟨hv0, hv1⟩ := hv'
  have hc' : ∀ g, ar.vcpu_capability a g = ok ⟨vcpuCapability g.bv⟩ := hc
  obtain ⟨hha, hho, hhp⟩ := hl
  unfold vcpu.init
  step with P1.obj.ks_get.spec as ⟨hd, ehd⟩
  have ehd' : hd = L.mem s (P1.vHeadA st s) := ehd
  simp only [vcpu.set, lift, bind_ok]
  have aN := (vw_of_off hv (o := vcpu.NEXT) (by rw [NEXT_val]; omega) (by rw [NEXT_val]) (by rw [NEXT_val]; omega)).2
  have vN := vfits_wadd hv (o := vcpu.NEXT) (by rw [NEXT_val]; omega)
  rw [NEXT_val] at vN
  refine WP.spec_bind (P1.LawfulStore.write_spec s _ _) fun s1 e1 => ?_
  subst e1
  -- s2: the old head's PREV word (outside the object)
  refine WP.spec_bind (Pₘ := fun s2 => L.ksb s2 = L.ksb s ∧ ∀ b, P1.Aligned b → v.val ≤ b.val →
      b.val < v.val + 32768 → L.mem s2 b = L.mem (L.wr s (core.num.U64.wrapping_add v vcpu.NEXT) hd) b) ?_
    fun s2 ⟨k2, h2⟩ => ?_
  · split
    · rename_i hn
      have hn' : L.mem s (P1.vHeadA st s) ≠ 0#u64 := by rw [← ehd']; simpa using hn
      obtain ⟨hpa, hpo⟩ := hhp hn'
      refine WP.spec_mono (P1.LawfulStore.write_spec _ _ _) fun s' e => ?_
      subst e
      have ea : core.num.U64.wrapping_add hd vcpu.PREV = vPrevA (L.mem s (P1.vHeadA st s)) := by rw [ehd']; rfl
      rw [ea]
      refine ⟨by simp, fun b hb h1 h2 => ?_⟩
      rw [P1.LawfulStore.mem_wr_ne hpa hb (by unfold OutV at hpo; omega)]
    · exact (WP.spec_ok _).2 ⟨by simp, fun _ _ _ _ => rfl⟩
  step with P1.obj.ks_set.spec as ⟨s3, e3⟩
  subst e3
  have ea : core.num.U64.wrapping_add (L.ksb s2) layout.ks.VCPU_HEAD = P1.vHeadA st s := by
    unfold P1.vHeadA; rw [k2]
  rw [ea, hc', bind_ok]
  have aX := (vw_of_off hv (o := vcpu.XCR0) (by rw [XCR0_val]; omega) (by rw [XCR0_val]) (by rw [XCR0_val]; omega)).2
  have vX := vfits_wadd hv (o := vcpu.XCR0) (by rw [XCR0_val]; omega)
  rw [XCR0_val] at vX
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s4 e4 => ?_
  subst e4
  refine WP.spec_bind (VirtInitIo.init_loop0_io hv _) fun s5 h5 => ?_
  rw [hvirt, bind_ok, if_pos hc2]
  refine WP.spec_bind (reset_svm_img hv s5) fun s6 ⟨f6, c6, v6⟩ => ?_
  simp only [shl_32, shl_24, EXC_eq, bind_ok, lift]
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s7 e7 => ?_
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s8 e8 => ?_
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s9 e9 => ?_
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s10 e10 => ?_
  refine WP.spec_mono (P1.LawfulStore.write_spec _ _ _) fun s11 e11 => ?_
  -- the words below `TCB` (the VMCS image) at s5: zero
  have hlow : ∀ b, P1.Aligned b → v.val ≤ b.val → b.val < v.val + 20480 → L.mem s5 b = 0#u64 := by
    intro b hb hb1 hb2
    have nI : ¬ VirtInitIo.IoR v b 1024 := by unfold VirtInitIo.IoR; omega
    rw [h5 b hb, if_neg nI, P1.LawfulStore.mem_wr_ne aX hb (by omega),
      P1.LawfulStore.mem_wr_ne hha hb (by unfold OutV at hho; omega), h2 b hb hb1 (by omega),
      P1.LawfulStore.mem_wr_ne aN hb (by omega), hz b hb hb1 (by omega)]
  -- the words from `TCB` on at s5
  open Classical in
  have hhigh : ∀ b, P1.Aligned b → v.val + 20480 ≤ b.val → b.val < v.val + 32768 →
      L.mem s5 b = if VirtInitIo.IoR v b 1024 then core.num.U64.MAX
        else if v.val + 20504 = b.val then (⟨vcpuCapability (0#u64).bv⟩ : U64)
        else if v.val + 20488 = b.val then hd else 0#u64 := by
    intro b hb hb1 hb2
    rw [h5 b hb]
    by_cases hI : VirtInitIo.IoR v b 1024
    · rw [if_pos hI, if_pos hI]
    · rw [if_neg hI, if_neg hI, P1.LawfulStore.mem_wr_val aX hb, vX]
      by_cases hX : v.val + 20504 = b.val
      · rw [if_pos hX, if_pos hX]
      · rw [if_neg hX, if_neg hX, P1.LawfulStore.mem_wr_ne hha hb (by unfold OutV at hho; omega),
          h2 b hb (by omega) (by omega), P1.LawfulStore.mem_wr_val aN hb, vN]
        by_cases hN : v.val + 20488 = b.val
        · rw [if_pos hN, if_pos hN]
        · rw [if_neg hN, if_neg hN]; exact hz b hb (by omega) hb2
  obtain ⟨b0a, b0v⟩ := wlit hv 0#u64 0 (by first | rfl | simp) (by norm_num) (by norm_num)
  obtain ⟨b8a, b8v⟩ := wlit hv 8#u64 8 (by first | rfl | simp) (by norm_num) (by norm_num)
  obtain ⟨b16a, b16v⟩ := wlit hv 16#u64 16 (by first | rfl | simp) (by norm_num) (by norm_num)
  obtain ⟨bIa, bIv⟩ := wlit hv vcpu.svm.INT_CTL 96 INTCTL_val (by norm_num) (by norm_num)
  obtain ⟨bNa, bNv⟩ := wlit hv vcpu.svm.NESTED_CTL 144 NESTED_val (by norm_num) (by norm_num)
  have hw : ∀ b, P1.Aligned b → v.val + 1768 ≤ b.val → L.mem s11 b = L.mem s6 b := by
    intro b hb hr
    rw [e11, P1.LawfulStore.mem_wr_ne bNa hb (by omega), e10, P1.LawfulStore.mem_wr_ne bIa hb (by omega),
      e9, P1.LawfulStore.mem_wr_ne b16a hb (by omega), e8, P1.LawfulStore.mem_wr_ne b8a hb (by omega),
      e7, P1.LawfulStore.mem_wr_ne b0a hb (by omega)]
  have H : ∀ b, P1.Aligned b → v.val + 20480 ≤ b.val → b.val < v.val + 32768 →
      L.mem s11 b = (open Classical in if VirtInitIo.IoR v b 1024 then core.num.U64.MAX
        else if v.val + 20504 = b.val then (⟨vcpuCapability (0#u64).bv⟩ : U64)
        else if v.val + 20488 = b.val then hd else 0#u64) := by
    intro b hb h1 h2'
    rw [hw b hb (by omega)]
    by_cases hc : b.val = v.val + 20536
    · have nI : ¬ VirtInitIo.IoR v b 1024 := by unfold VirtInitIo.IoR; omega
      have n1 : ¬ (v.val + 20504 = b.val) := by omega
      have n2 : ¬ (v.val + 20488 = b.val) := by omega
      rw [c6 b hb hc, if_neg nI, if_neg n1, if_neg n2]
    · rw [f6 b hb (Or.inr (by omega)) hc, hhigh b hb h1 h2']
  have hfin : ∀ o, o % 8 = 0 → o < 1768 → L.mem s11 (vo v o) = svmImgU o := by
    intro o ho8 hol
    have vb := voN hv (o := o) (by omega)
    have hb : P1.Aligned (vo v o) := by unfold P1.Aligned; rw [vb]; omega
    have h6o : L.mem s6 (vo v o) = if 1024 ≤ o then svmSaveU o else 0#u64 := by
      by_cases hlo : 1024 ≤ o
      · rw [if_pos hlo, v6 o ho8 hlo hol]
      · rw [if_neg hlo, f6 _ hb (Or.inl (by rw [vb]; omega)) (by rw [vb]; omega),
          hlow _ hb (by rw [vb]; omega) (by rw [vb]; omega)]
    rw [e11, P1.LawfulStore.mem_wr_val bNa hb, e10, P1.LawfulStore.mem_wr_val bIa hb,
      e9, P1.LawfulStore.mem_wr_val b16a hb, e8, P1.LawfulStore.mem_wr_val b8a hb,
      e7, P1.LawfulStore.mem_wr_val b0a hb, h6o]
    simp only [bNv, bIv, b16v, b8v, b0v, vb, Nat.add_left_cancel_iff]
    rfl
  refine { initCommon_of hv H with vmcb := fun off hr _ _ => ?_ }
  obtain ⟨h8, hl'⟩ := readable_nat hr
  have e : (⟨v.bv + off⟩ : U64) = vo v off.toNat := by
    unfold vo
    congr 2
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt off.isLt]
  have t := svm_tab (off.toNat / 8) (by omega)
  rw [show 8 * (off.toNat / 8) = off.toNat by omega] at t
  have eo : BitVec.ofNat 64 off.toNat = off := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt off.isLt]
  rw [eo] at t
  show (L.mem s11 ⟨v.bv + off⟩).bv = _
  rw [e, hfin _ h8 hl', t]

/-! ## Retype → init against the spec's `initVcpu` -/

/-- **`VirtCodeAgree` [P]**: FL4's `Arch::virtualization()` reports code 2 exactly when the spec's backend is SVM
(fl4-arch-x86_64 `vm::backend()`, fixed at boot; the same fact as mmuAD's `ZvVirtAgree`). Holds on the existing
top's platform (`virtualization() = 0`, `virtKind = .none`). -/
def VirtCodeAgree (ar : machine.Arch A) (a : A) : Prop :=
  ∃ c, ar.virtualization a = ok c ∧ (c = 2#u64 ↔ virtKind = .svm)

theorem initVcpu_ne_svm {k : VirtKind} (h : k ≠ .svm) : initVcpu k = initVcpu .vmx := by
  unfold initVcpu; simp [h]

/-- **`vcpu::init` relates to `initVcpu .vmx`** (VMX backend). -/
theorem init_rel_vmx (hc : CapAgree ar a) {c : U64} (hvirt : ar.virtualization a = ok c) (hc2 : c ≠ 2#u64)
    {v : U64} (hv : VFits v) (s : S) (hz : VZero st s v) (hl : InitListOut st s v) :
    vcpu.init st ar s a v ⦃ s' => VcpuRelVmx (memW st s') v.bv (initVcpu .vmx) ⦄ :=
  WP.spec_mono (init_vmx_img hc hvirt hc2 hv s hz hl) fun _ h => vcpuRelVmx_init h

/-- **`vcpu::init` relates to `initVcpu .svm`** (SVM backend). -/
theorem init_rel_svm (hc : CapAgree ar a) {c : U64} (hvirt : ar.virtualization a = ok c) (hc2 : c = 2#u64)
    {v : U64} (hv : VFits v) (s : S) (hz : VZero st s v) (hl : InitListOut st s v) :
    vcpu.init st ar s a v ⦃ s' => VcpuRelSvm (memW st s') v.bv (initVcpu .svm) ⦄ :=
  WP.spec_mono (init_svm_img hc hvirt hc2 hv s hz hl) fun _ h => vcpuRelSvm_init h

/-- **Retype → init on the spec's backend** (`fl4InvokeUntypedV`'s `initVcpu virtKind`): under `VirtCodeAgree` [P],
the VCPU FL4's `init` leaves in a zeroed object relates to `initVcpu virtKind` on that backend. -/
theorem init_rel (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {v : U64} (hv : VFits v) (s : S)
    (hz : VZero st s v) (hl : InitListOut st s v) :
    vcpu.init st ar s a v ⦃ s' => (virtKind = .svm → VcpuRelSvm (memW st s') v.bv (initVcpu virtKind)) ∧
      (virtKind ≠ .svm → VcpuRelVmx (memW st s') v.bv (initVcpu virtKind)) ⦄ := by
  obtain ⟨c, hvirt, hiff⟩ := hk
  by_cases h2 : c = 2#u64
  · have hk' := hiff.1 h2
    exact WP.spec_mono (init_rel_svm hc hvirt h2 hv s hz hl) fun _ h => ⟨fun _ => hk' ▸ h, fun hn => absurd hk' hn⟩
  · have hk' : virtKind ≠ .svm := fun e => h2 (hiff.2 e)
    exact WP.spec_mono (init_rel_vmx hc hvirt h2 hv s hz hl) fun _ h =>
      ⟨fun e => absurd e hk', fun _ => by rw [initVcpu_ne_svm hk']; exact h⟩

end

end
end Fl4Proofs.P3.VirtInitWalk
