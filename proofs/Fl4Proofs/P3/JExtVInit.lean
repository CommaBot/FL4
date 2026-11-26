/-
P3 (line mmuAD, gen 22): **the footprint of `vcpu::init`, and `JExtV.grow` on the extracted VT-x VCPU creation.**

* `VFits v`: a VCPU address, 2^15-aligned and fitting (as `JVLay`'s VCPUs). `vw_of_off` / `vw_of_val`: the words
  of a VCPU at offsets below 2^15 other than `TCB` (20480) are `VW v` words and aligned.
* `vset_w`, `vmcs_w`: `vcpu.set` / `vcpu.write_vmcs` of such a word keep a footprint containing `VW v`.
* `vcpu.init_loop0.foot` (the 1024 IO-bitmap words), `vcpu.init_loop1.foot` (the `WRITE_FIELDS` VMCS writes),
  `vcpu.reset_svm_loop.foot` and `vcpu.reset_svm.foot` (the VMCB: `SVM_CPU`, the zeroed save area
  `[v + 1024, v + 1768)`, the segment attributes and the save-area registers).
* **`vcpu.init.foot`**: `vcpu::init` (vcpu.rs l. 644-678) writes only `InitW s v` — the VCPU's own `VW v` words,
  the list head word `VCPU_HEAD` (`P1.vHeadA`) and, when the list was not empty, the old head's `PREV` word. It
  never writes the new VCPU's `TCB` word (offset 20480). Premise `hh` [J]: those two list words are aligned (the
  head word lies in the kernel-global area, the old head is a 2^15-aligned VCPU).
* **`create_vcpu_grow`**: `objects.create_arch_object … X86Vcpu v` returns `Cap.Vcpu v` and `JExtV.grow` holds:
  `JExtV (insert v V) X th'` at its end. Premises: `JWPl` [J] (P3/JExtVLay derives it), `hd` [J] (the init
  footprint misses `JW V th`: the new object is fresh, apart from every slot, TCB and old VCPU — the retype's
  freshness — and the list words are no `JW` words), `hko` [J] (the new `TCB` word is neither list word), `htc` /
  `hsl` (the typed heap `th'` keeps `th`'s TCBs and slots: the retype's typed-heap step), and **`hz`: the new VCPU's
  `TCB` word is 0 at the call** — "retype zeroes the object".
* **`create_vcpu_grow_win`**: `hz` from P3's `WinZero` (UntypedFrameBase: the window after a retype's clearing,
  aligned words zero, with no TCB exception for a VCPU retype), so the zeroing is the retype's own fact.

No [P] / [W] / [S] premise; no existing statement changed.
-/
import Fl4Proofs.P3.JExtVSig
import Fl4Proofs.P3.UntypedFrameBase
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P0.Consts

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {V X : Set U64} {th : TypedHeap}

/-- A VCPU address: 2^15-aligned, and the object fits. -/
def VFits (v : U64) : Prop := v.val % 32768 = 0 ∧ v.val + 32768 ≤ 2 ^ 64

theorem vfits_wadd {v o : U64} (hv : VFits v) (h1 : o.val < 32768) :
    (core.num.U64.wrapping_add v o).val = v.val + o.val := by
  obtain ⟨hv1, hv2⟩ := hv
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

theorem vw_of_off {v o : U64} (hv : VFits v) (h1 : o.val < 32768) (h2 : o.val % 8 = 0) (h3 : o.val ≠ 20480) :
    VW v (core.num.U64.wrapping_add v o) ∧ P1.Aligned (core.num.U64.wrapping_add v o) := by
  refine ⟨⟨o, h1, h2, h3, rfl⟩, ?_⟩
  have e := vfits_wadd hv h1
  obtain ⟨hv1, hv2⟩ := hv
  unfold P1.Aligned; rw [e]; omega

theorem vw_of_val {v b : U64} (hv : VFits v) (hb : P1.Aligned b) (h1 : v.val ≤ b.val) (h2 : b.val < v.val + 32768)
    (h3 : b.val ≠ v.val + 20480) : VW v b := by
  have hb64 : b.val < 2 ^ 64 := b.bv.isLt
  have e : (⟨BitVec.ofNat 64 (b.val - v.val)⟩ : U64).val = b.val - v.val := by
    show (BitVec.ofNat 64 (b.val - v.val)).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hv' := hv
  obtain ⟨hv1, hv2⟩ := hv'
  unfold P1.Aligned at hb
  refine ⟨⟨BitVec.ofNat 64 (b.val - v.val)⟩, by rw [e]; omega, by rw [e]; omega, by rw [e]; omega, ?_⟩
  apply UScalar.eq_of_val_eq
  rw [vfits_wadd hv (by rw [e]; omega), e]; omega

/-- The VCPU's `TCB` word is no `VW` word. -/
theorem not_vw_tcb {v : U64} (hv : VFits v) : ¬ VW v (vTcbA v) := by
  rintro ⟨o, h1, h2, h3, e⟩
  have e1 := vfits_wadd hv h1
  have e2 : (vTcbA v).val = v.val + 20480 := by
    unfold vTcbA; rw [vfits_wadd hv (by simp [vcpu.TCB])]; simp [vcpu.TCB]
  have := congrArg UScalar.val e
  rw [e1, e2] at this; omega

/-- `WritesIn.mono` over the aligned words only. -/
theorem wi_mono_al {s s' : S} {P Q : U64 → Prop} (h : P1.WritesIn st s s' P) (hPQ : ∀ b, P1.Aligned b → P b → Q b) :
    P1.WritesIn st s s' Q :=
  ⟨h.1, h.2.1, fun b hb hn => h.2.2 b hb fun h' => hn (hPQ b hb h')⟩

theorem vset_w {s0 s1 : S} {v : U64} {W : U64 → Prop} (hv : VFits v) (hW : ∀ b, VW v b → W b)
    (h : P1.WritesIn st s0 s1 W) (o x : U64) (h1 : o.val < 32768) (h2 : o.val % 8 = 0) (h3 : o.val ≠ 20480) :
    vcpu.set st s1 v o x ⦃ s' => P1.WritesIn st s0 s' W ⦄ := by
  obtain ⟨hb, ha⟩ := vw_of_off hv h1 h2 h3
  unfold vcpu.set
  simp only [lift, bind_ok]
  exact WP.spec_mono (P1.LawfulStore.write_spec s1 _ _) fun s' e => by
    subst e
    exact (h.trans (P1.writesIn_wr ha)).mono fun b hb' => hb'.elim id fun e => e ▸ hW _ hb

theorem vmcs_w {s0 s1 : S} {v : U64} {W : U64 → Prop} (hv : VFits v) (hW : ∀ b, VW v b → W b)
    (h : P1.WritesIn st s0 s1 W) (f x : U64) :
    vcpu.write_vmcs st s1 v f x ⦃ s' => P1.WritesIn st s0 s' W ⦄ := by
  unfold vcpu.write_vmcs
  refine WP.spec_bind (P1.vcpu.vmcs_addr.off v f) ?_
  rintro _ ⟨o, h1, h2, rfl⟩
  obtain ⟨hb, ha⟩ := vw_of_off hv (o := o) (by omega) h2 (by omega)
  exact WP.spec_mono (P1.LawfulStore.write_spec s1 _ _) fun s' e => by
    subst e
    exact (h.trans (P1.writesIn_wr ha)).mono fun b hb' => hb'.elim id fun e => e ▸ hW _ hb

/-- `init`'s IO-bitmap loop writes `VW v` words. -/
theorem vcpu.init_loop0.foot {s0 : S} {v : U64} {W : U64 → Prop} (hv : VFits v) (hW : ∀ b, VW v b → W b)
    (s : S) (i : U64) (h : P1.WritesIn st s0 s W) :
    vcpu.init_loop0 st s v i ⦃ s' => P1.WritesIn st s0 s' W ⦄ := by
  unfold vcpu.init_loop0
  apply loop.spec_decr_nat (measure := fun x : S × U64 => 1024 - x.2.val)
    (inv := fun x => P1.WritesIn st s0 x.1 W)
  · rintro ⟨x0, x1⟩ hx
    simp only at hx
    dsimp only
    unfold vcpu.init_loop0.body
    split
    · rename_i hlt
      have hlt' : x1.val < 1024 := by simpa using hlt
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      have hio : i2.val = 24576 + i1.val := by rw [hi2]; simp [vcpu.IO]
      refine WP.spec_bind (vset_w hv hW hx i2 _ (by omega) (by omega) (by omega)) fun s1 w1 => ?_
      step as ⟨i3, hi3⟩
      exact ⟨w1, by scalar_tac⟩
    · exact (WP.spec_ok _).2 hx
  · exact h

/-- `init`'s VMCS loop writes `VW v` words. -/
theorem vcpu.init_loop1.foot (hA : P0.ArchTotal ar) {s0 : S} {v : U64} {W : U64 → Prop} (hv : VFits v)
    (hW : ∀ b, VW v b → W b) (s : S) (a : A) (j : Usize) (h : P1.WritesIn st s0 s W) :
    vcpu.init_loop1 st ar s a v j ⦃ s' => P1.WritesIn st s0 s' W ⦄ := by
  unfold vcpu.init_loop1
  apply loop.spec_decr_nat (measure := fun x : S × Usize => 73 - x.2.val)
    (inv := fun x => P1.WritesIn st s0 x.1 W)
  · rintro ⟨x0, x1⟩ hx
    simp only at hx
    dsimp only
    unfold vcpu.init_loop1.body
    simp only [lift, bind_ok]
    split
    · rename_i hlt
      step as ⟨f, _⟩
      refine WP.spec_bind (P0.vcpu.sanitize_vmcs.p0 _ _ _ _ hA) fun r _ => ?_
      refine WP.spec_bind (Pₘ := fun s2 => P1.WritesIn st s0 s2 W) ?_ fun s2 h2 => ?_
      · split
        · exact vmcs_w hv hW hx _ _
        · exact (WP.spec_ok _).2 hx
      step as ⟨j1, hj1⟩
      exact ⟨h2, by scalar_tac⟩
    · exact (WP.spec_ok _).2 hx
  · exact h

/-- The VMCB segment-attribute loop writes `VW v` words. -/
theorem vcpu.reset_svm_loop.foot {s0 : S} {v : U64} {W : U64 → Prop} (hv : VFits v) (hW : ∀ b, VW v b → W b)
    (s : S) (off : U64) (h8 : off.val % 8 = 0) (h : P1.WritesIn st s0 s W) :
    vcpu.reset_svm_loop st s v off ⦃ s' => P1.WritesIn st s0 s' W ⦄ := by
  unfold vcpu.reset_svm_loop
  apply loop.spec_decr_nat (measure := fun x : S × U64 => 1169 - x.2.val)
    (inv := fun x => x.2.val % 8 = 0 ∧ P1.WritesIn st s0 x.1 W)
  · rintro ⟨x0, x1⟩ ⟨hx8, hx⟩
    simp only at hx hx8
    dsimp only
    unfold vcpu.reset_svm_loop.body
    split
    · rename_i hle
      have hle' : x1.val ≤ 1168 := by simpa using hle
      refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun attr _ => ?_
      · repeat' split
        all_goals exact (WP.spec_ok _).2 trivial
      step as ⟨i, _⟩
      simp only [lift, bind_ok]
      refine WP.spec_bind (vset_w hv hW hx x1 _ (by omega) hx8 (by omega)) fun s1 w1 => ?_
      step as ⟨off1, hoff1⟩
      first
        | exact ⟨⟨by omega, w1⟩, by scalar_tac⟩
        | omega
        | scalar_tac
    · exact (WP.spec_ok _).2 hx
  · exact ⟨h8, h⟩

/-- `reset_svm` writes `VW v` words (module docstring). -/
theorem vcpu.reset_svm.foot {s0 : S} {v : U64} {W : U64 → Prop} (hv : VFits v) (hW : ∀ b, VW v b → W b)
    (s : S) (h : P1.WritesIn st s0 s W) :
    vcpu.reset_svm st s v ⦃ s' => P1.WritesIn st s0 s' W ⦄ := by
  have hv' := hv
  obtain ⟨hv1, hv2⟩ := hv'
  unfold vcpu.reset_svm
  refine WP.spec_bind (vset_w hv hW h vcpu.SVM_CPU 0#u64 (by simp [vcpu.SVM_CPU]) (by simp [vcpu.SVM_CPU])
    (by simp [vcpu.SVM_CPU])) fun s1 w1 => ?_
  simp only [lift, bind_ok]
  step with vcpu.svm.END.spec as ⟨i1, e1⟩
  subst e1
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = 744 := by scalar_tac
  have hp : (core.num.U64.wrapping_add v 1024#u64).val = v.val + 1024 := vfits_wadd hv (by simp)
  refine WP.spec_bind (P1.LawfulStore.zero_spec s1 _ _) fun s2 e2 => ?_
  subst e2
  have z : P1.WritesIn st s1 (L.zr s1 (core.num.U64.wrapping_add v 1024#u64) i2)
      (fun b => (core.num.U64.wrapping_add v 1024#u64).val ≤ b.val ∧
        b.val < (core.num.U64.wrapping_add v 1024#u64).val + i2.val) :=
    ⟨L.ksb_zr _ _ _, L.cpu_zr _ _ _, fun b hb hnb => by
      rw [L.mem_zr _ _ _ _ (by unfold P1.Aligned; rw [hp]; omega) (by omega) (by rw [hp]; omega) hb, if_neg hnb]⟩
  have w2 := wi_mono_al (w1.trans z) fun b hb hh => hh.elim id fun hr =>
    hW _ (vw_of_val hv hb (by omega) (by omega) (by omega))
  refine WP.spec_bind (vcpu.reset_svm_loop.foot hv hW _ 1024#u64 (by simp) w2) fun s3 w3 => ?_
  refine WP.spec_bind (vset_w hv hW w3 1040#u64 _ (by simp) (by simp) (by simp)) fun s4 w4 => ?_
  refine WP.spec_bind (vset_w hv hW w4 1048#u64 _ (by simp) (by simp) (by simp)) fun s5 w5 => ?_
  step as ⟨i3, _⟩
  step with vcpu.svm.EFER.spec as ⟨i4, e4⟩
  subst e4
  refine WP.spec_bind (vset_w hv hW w5 1232#u64 _ (by simp) (by simp) (by simp)) fun s6 w6 => ?_
  step with vcpu.svm.CR0.spec as ⟨i5, e5⟩
  subst e5
  refine WP.spec_bind (vset_w hv hW w6 1368#u64 _ (by simp) (by simp) (by simp)) fun s7 w7 => ?_
  step with vcpu.svm.DR6.spec as ⟨i6, e6⟩
  subst e6
  refine WP.spec_bind (vset_w hv hW w7 1384#u64 _ (by simp) (by simp) (by simp)) fun s8 w8 => ?_
  step with vcpu.svm.DR7.spec as ⟨i7, e7⟩
  subst e7
  refine WP.spec_bind (vset_w hv hW w8 1376#u64 _ (by simp) (by simp) (by simp)) fun s9 w9 => ?_
  step with vcpu.svm.RFLAGS.spec as ⟨i8, e8⟩
  subst e8
  refine WP.spec_bind (vset_w hv hW w9 1392#u64 _ (by simp) (by simp) (by simp)) fun s10 w10 => ?_
  step with vcpu.svm.RIP.spec as ⟨i9, e9⟩
  subst e9
  refine WP.spec_bind (vset_w hv hW w10 1400#u64 _ (by simp) (by simp) (by simp)) fun s11 w11 => ?_
  step with vcpu.svm.G_PAT.spec as ⟨i10, e10⟩
  subst e10
  exact vset_w hv hW w11 1640#u64 _ (by simp) (by simp) (by simp)

/-- **`vcpu::init`'s words** (module docstring): the VCPU's own words, the list head word, the old head's
`PREV` word. -/
def InitW (st : machine.Store S) [L : P1.LawfulStore st] (s : S) (v b : U64) : Prop :=
  VW v b ∨ b = P1.vHeadA st s ∨
    (L.mem s (P1.vHeadA st s) ≠ 0#u64 ∧ b = vPrevA (L.mem s (P1.vHeadA st s)))

/-- **The footprint of `vcpu::init`** (module docstring). `hh` [J]: the list head word and the old head's
`PREV` word are aligned. -/
theorem vcpu.init.foot (hA : P0.ArchTotal ar) (s : S) (a : A) {v : U64} (hv : VFits v)
    (hh : P1.Aligned (P1.vHeadA st s) ∧
      (L.mem s (P1.vHeadA st s) ≠ 0#u64 → P1.Aligned (vPrevA (L.mem s (P1.vHeadA st s))))) :
    vcpu.init st ar s a v ⦃ s' => P1.WritesIn st s s' (InitW st s v) ⦄ := by
  have hW : ∀ b, VW v b → InitW st s v b := fun b h => Or.inl h
  unfold vcpu.init
  step with P1.obj.ks_get.spec as ⟨hd, ehd⟩
  have ehd' : hd = L.mem s (P1.vHeadA st s) := ehd
  refine WP.spec_bind (vset_w hv hW (P1.WritesIn.refl s _) vcpu.NEXT hd (by simp [vcpu.NEXT]) (by simp [vcpu.NEXT])
    (by simp [vcpu.NEXT])) fun s1 w1 => ?_
  refine WP.spec_bind (Pₘ := fun s2 => P1.WritesIn st s s2 (InitW st s v)) ?_ fun s2 w2 => ?_
  · split
    · rename_i hn
      have hn' : L.mem s (P1.vHeadA st s) ≠ 0#u64 := by rw [← ehd']; simpa using hn
      unfold vcpu.set
      simp only [lift, bind_ok]
      refine WP.spec_mono (P1.LawfulStore.write_spec s1 _ _) fun s' e => ?_
      subst e
      have ea : core.num.U64.wrapping_add hd vcpu.PREV = vPrevA (L.mem s (P1.vHeadA st s)) := by rw [ehd']; rfl
      rw [ea]
      exact (w1.trans (P1.writesIn_wr (hh.2 hn'))).mono fun b h => h.elim id fun e => Or.inr (Or.inr ⟨hn', e⟩)
    · exact (WP.spec_ok _).2 w1
  refine WP.spec_bind (P1.obj.ks_set.spec s2 _ _) fun s3 e3 => ?_
  subst e3
  have ea : core.num.U64.wrapping_add (L.ksb s2) layout.ks.VCPU_HEAD = P1.vHeadA st s := by
    unfold P1.vHeadA; rw [w2.1]
  have w3 : P1.WritesIn st s (L.wr s2 (core.num.U64.wrapping_add (L.ksb s2) layout.ks.VCPU_HEAD) v)
      (InitW st s v) := by
    rw [ea]; exact (w2.trans (P1.writesIn_wr hh.1)).mono fun b h => h.elim id fun e => Or.inr (Or.inl e)
  refine WP.spec_bind (hA.vcpu_capability a 0#u64) fun i _ => ?_
  refine WP.spec_bind (vset_w hv hW w3 vcpu.XCR0 i (by simp [vcpu.XCR0]) (by simp [vcpu.XCR0])
    (by simp [vcpu.XCR0])) fun s4 w4 => ?_
  refine WP.spec_bind (vcpu.init_loop0.foot hv hW s4 0#u64 w4) fun s5 w5 => ?_
  refine WP.spec_bind (hA.virtualization a) fun i1 _ => ?_
  split
  · refine WP.spec_bind (vcpu.reset_svm.foot hv hW s5 w5) fun s6 w6 => ?_
    refine WP.spec_bind (vset_w hv hW w6 0#u64 _ (by simp) (by simp) (by simp)) fun s7 w7 => ?_
    step as ⟨i2, _⟩
    step with vcpu.EXCEPTIONS.spec as ⟨i3, _⟩
    simp only [lift, bind_ok]
    refine WP.spec_bind (vset_w hv hW w7 8#u64 _ (by simp) (by simp) (by simp)) fun s8 w8 => ?_
    refine WP.spec_bind (vset_w hv hW w8 16#u64 _ (by simp) (by simp) (by simp)) fun s9 w9 => ?_
    step as ⟨i5, _⟩
    refine WP.spec_bind (vset_w hv hW w9 vcpu.svm.INT_CTL _ (by simp [vcpu.svm.INT_CTL])
      (by simp [vcpu.svm.INT_CTL]) (by simp [vcpu.svm.INT_CTL])) fun s10 w10 => ?_
    exact vset_w hv hW w10 vcpu.svm.NESTED_CTL _ (by simp [vcpu.svm.NESTED_CTL]) (by simp [vcpu.svm.NESTED_CTL])
      (by simp [vcpu.svm.NESTED_CTL])
  · refine WP.spec_bind (vcpu.init_loop1.foot hA hv hW s5 a 0#usize w5) fun s6 w6 => ?_
    step as ⟨i2, _⟩
    refine WP.spec_bind (P0.vcpu.sanitize_vmcs.p0 _ _ _ _ hA) fun r _ => ?_
    simp only [lift, bind_ok]
    refine WP.spec_bind (vmcs_w hv hW w6 _ _) fun s7 w7 => ?_
    refine WP.spec_bind (vmcs_w hv hW w7 _ _) fun s8 w8 => ?_
    exact vmcs_w hv hW w8 _ _

/-- `init` never writes the new VCPU's `TCB` word (`hko` [J]: it is neither list word). -/
theorem vcpu.init.tcb0 (hA : P0.ArchTotal ar) (s : S) (a : A) {v : U64} (hv : VFits v)
    (hh : P1.Aligned (P1.vHeadA st s) ∧
      (L.mem s (P1.vHeadA st s) ≠ 0#u64 → P1.Aligned (vPrevA (L.mem s (P1.vHeadA st s)))))
    (hko : vTcbA v ≠ P1.vHeadA st s ∧ (L.mem s (P1.vHeadA st s) ≠ 0#u64 → vTcbA v ≠ vPrevA (L.mem s (P1.vHeadA st s)))) :
    vcpu.init st ar s a v ⦃ s' => P1.WritesIn st s s' (InitW st s v) ∧ L.mem s' (vTcbA v) = L.mem s (vTcbA v) ⦄ :=
  WP.spec_mono (vcpu.init.foot hA s a hv hh) fun s' w => by
    refine ⟨w, w.mem_eq ?_ ?_⟩
    · have e2 : (vTcbA v).val = v.val + 20480 := by
        unfold vTcbA; rw [vfits_wadd hv (by simp [vcpu.TCB])]; simp [vcpu.TCB]
      obtain ⟨hv1, -⟩ := hv
      unfold P1.Aligned; rw [e2]; omega
    · rintro (h | e | ⟨hn, e⟩)
      · exact not_vw_tcb hv h
      · exact hko.1 e
      · exact hko.2 hn e

set_option maxHeartbeats 4000000 in
/-- **The VT-x VCPU creation grows `V`** (`JExtV.grow` on `objects.create_arch_object … X86Vcpu`; module
docstring). Premises `P`, `hh`, `hko`, `hd` [J]; `hz`: the retype left the new `TCB` word zero. -/
theorem create_vcpu_grow (hA : P0.ArchTotal ar) {s : S} (E : JExtV (L := L) V X th s) (P : JWPl V th) (a : A)
    {v : U64} (hv0 : v ≠ 0#u64) (hv : VFits v)
    (hh : P1.Aligned (P1.vHeadA st s) ∧
      (L.mem s (P1.vHeadA st s) ≠ 0#u64 → P1.Aligned (vPrevA (L.mem s (P1.vHeadA st s)))))
    (hko : vTcbA v ≠ P1.vHeadA st s ∧ (L.mem s (P1.vHeadA st s) ≠ 0#u64 → vTcbA v ≠ vPrevA (L.mem s (P1.vHeadA st s))))
    (hd : ∀ b, InitW st s v b → ¬ JW V th b) (hz : L.mem s (vTcbA v) = 0#u64)
    {th' : TypedHeap} (htc : ∀ t, th' t = some .tcb ↔ th t = some .tcb) (hsl : ∀ y, IsSlot th' y → IsSlot th y)
    (dev : Bool) :
    objects.create_arch_object st ar s a fl4_abi.consts.object.X86Vcpu v dev ⦃ r =>
      r.1 = capability.Cap.Vcpu v ∧ JExtV (L := L) (insert v V) X th' r.2.1 ⦄ := by
  unfold objects.create_arch_object
  rw [if_pos rfl]
  refine WP.spec_bind (vcpu.init.tcb0 hA s a hv hh hko) fun s1 ⟨w, e⟩ => ?_
  exact (WP.spec_ok _).2 ⟨rfl, E.grow P hv0 htc hsl w hd (by rw [e]; exact hz)⟩

/-- **`create_vcpu_grow` with the zeroing from the retype's window** (`WinZero`, P3/UntypedFrameBase, with no
TCB exception): the new `TCB` word lies in the cleared window. -/
theorem create_vcpu_grow_win (hA : P0.ArchTotal ar) {s : S} (E : JExtV (L := L) V X th s) (P : JWPl V th) (a : A)
    {v : U64} (hv0 : v ≠ 0#u64) (hv : VFits v)
    (hh : P1.Aligned (P1.vHeadA st s) ∧
      (L.mem s (P1.vHeadA st s) ≠ 0#u64 → P1.Aligned (vPrevA (L.mem s (P1.vHeadA st s)))))
    (hko : vTcbA v ≠ P1.vHeadA st s ∧ (L.mem s (P1.vHeadA st s) ≠ 0#u64 → vTcbA v ≠ vPrevA (L.mem s (P1.vHeadA st s))))
    (hd : ∀ b, InitW st s v b → ¬ JW V th b) {A0 k win : Nat} (hwz : WinZero (L.mem s) A0 k win False)
    (hin : A0 ≤ v.val + 20480 ∧ v.val + 20480 < A0 + win * k)
    {th' : TypedHeap} (htc : ∀ t, th' t = some .tcb ↔ th t = some .tcb) (hsl : ∀ y, IsSlot th' y → IsSlot th y)
    (dev : Bool) :
    objects.create_arch_object st ar s a fl4_abi.consts.object.X86Vcpu v dev ⦃ r =>
      r.1 = capability.Cap.Vcpu v ∧ JExtV (L := L) (insert v V) X th' r.2.1 ⦄ := by
  have e2 : (vTcbA v).val = v.val + 20480 := by
    unfold vTcbA; rw [vfits_wadd hv (by simp [vcpu.TCB])]; simp [vcpu.TCB]
  have hal : P1.Aligned (vTcbA v) := by
    obtain ⟨hv1, -⟩ := hv
    unfold P1.Aligned; rw [e2]; omega
  have hz : L.mem s (vTcbA v) = 0#u64 :=
    (hwz _ hal (by rw [e2]; exact hin.1) (by rw [e2]; exact hin.2)).resolve_right fun h => h.1
  exact create_vcpu_grow hA E P a hv0 hv hh hko hd hz htc hsl dev

end

end

end Fl4Proofs.P3
